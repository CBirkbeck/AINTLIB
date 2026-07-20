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
* `IsLocalizedModule.exists_sub_liftOfLE_eq_of_span_eq_top` — the **finite basic cover** version:
  for `f : ι → R` (`ι` finite) generating the unit ideal and an additive Čech `1`-cocycle
  `c i j` over the pairwise overlaps `D(fᵢ) ∩ D(fⱼ)` (cocycle condition on triple overlaps),
  there are `a i` over `D(fᵢ)` with `c i j = a i - a j` restricted — Čech `H¹` vanishing for
  the full finite cover, by the standard partition-of-unity weighted average.
* `IsLocalizedModule.liftOfLE_liftOfLE`, `exists_liftOfLE_eq_pow_smul`,
  `exists_pow_smul_eq_zero_of_liftOfLE_eq_zero` — the restriction-composition, power
  denominator-clearing and power torsion-killing toolkit backing the finite-cover proof.
* `IsLocalizedModule.isLocalizedModule_sup_sup_of_powers_mul` — triple-product form of the
  `powers (f * g)` bridge, for consumers holding triple overlaps as `Away (fᵢ * fⱼ * fₖ)`.

## Implementation notes

The overlap `M_{fg}` is localized at the **join** submonoid `Submonoid.powers f ⊔ Submonoid.powers g`
rather than `Submonoid.powers (f * g)`; the two are the same localization, but the join makes the
restriction maps literal `IsLocalizedModule.liftOfLE` maps (`Submonoid.powers f ≤ …`), which keeps
the fraction bookkeeping clean.  The bridge
`IsLocalizedModule.isLocalizedModule_sup_of_powers_mul` re-expresses a `Submonoid.powers (f * g)`
localization as a join localization, so a consumer holding `M[1/(fg)]` in the `powers (f*g)` form
can still apply the theorem.

The **general finite cover** version (an arbitrary family generating the unit ideal, with the full
`c i j + c j k = c i k` cocycle condition on triple overlaps) is
`exists_sub_liftOfLE_eq_of_span_eq_top` below.  Its proof is the standard weighted-average
partition-of-unity argument (Hartshorne III.4.5 / Stacks 01X9): clear the `k`-denominator of each
`c i k` at a uniform power `N` (`exists_liftOfLE_eq_pow_smul`), observe that the resulting triple
defect dies in the triple localization by the cocycle law and hence is killed by a power `Γ` of
`f k` (`exists_pow_smul_eq_zero_of_liftOfLE_eq_zero`), and average against a partition of unity
`∑ k, g k * f k ^ (Γ + N) = 1` (`Ideal.span_pow_eq_top`).
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

namespace IsLocalizedModule

section Toolkit

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Restriction (`liftOfLE`) maps between localized modules compose: restricting from `S₁` to `S₂`
and then to `S₃` is restricting from `S₁` to `S₃`.  The final inclusion is taken as a separate
argument `h₃` so both orientations rewrite cleanly (all proofs of `S₁ ≤ S₃` are definitionally
equal). -/
theorem liftOfLE_liftOfLE {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (S₁ S₂ S₃ : Submonoid R) (h₁ : S₁ ≤ S₂) (h₂ : S₂ ≤ S₃) (h₃ : S₁ ≤ S₃)
    (l₁ : M →ₗ[R] M₁) (l₂ : M →ₗ[R] M₂) (l₃ : M →ₗ[R] M₃)
    [IsLocalizedModule S₁ l₁] [IsLocalizedModule S₂ l₂] [IsLocalizedModule S₃ l₃] (x : M₁) :
    liftOfLE S₂ S₃ h₂ l₂ l₃ (liftOfLE S₁ S₂ h₁ l₁ l₂ x) = liftOfLE S₁ S₃ h₃ l₁ l₃ x := by
  obtain ⟨m, s, rfl⟩ : ∃ (m : M) (s : S₁), mk' l₁ m s = x := by
    obtain ⟨⟨m, s⟩, h⟩ := mk'_surjective S₁ l₁ x
    exact ⟨m, s, h⟩
  rw [liftOfLE_mk', liftOfLE_mk', liftOfLE_mk']

/-- **Power denominator-clearing.**  Every element of the localization of `M` at the join
`S₁ ⊔ powers g` becomes, after multiplication by a suitable power `g ^ n`, the restriction of an
element of the localization at `S₁` alone. -/
theorem exists_liftOfLE_eq_pow_smul {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (S₁ : Submonoid R) (g : R) (l₁ : M →ₗ[R] M₁) (l₂ : M →ₗ[R] M₂)
    [IsLocalizedModule S₁ l₁] [IsLocalizedModule (S₁ ⊔ Submonoid.powers g) l₂] (c : M₂) :
    ∃ (n : ℕ) (b : M₁),
      liftOfLE S₁ (S₁ ⊔ Submonoid.powers g) le_sup_left l₁ l₂ b = g ^ n • c := by
  obtain ⟨m, s, rfl⟩ : ∃ (m : M) (s : ↥(S₁ ⊔ Submonoid.powers g)), mk' l₂ m s = c := by
    obtain ⟨⟨m, s⟩, h⟩ := mk'_surjective (S₁ ⊔ Submonoid.powers g) l₂ c
    exact ⟨m, s, h⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := Submonoid.mem_sup.mp s.2
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff y g).mp hy
  refine ⟨n, mk' l₁ m ⟨x, hx⟩, ?_⟩
  rw [liftOfLE_mk', ← mk'_smul, mk'_eq_mk'_iff]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_smul]
  rw [← hxy]

/-- **Power torsion-killing.**  If an element of the localization of `M` at `P` dies in the
further localization at `P ⊔ powers g`, it is killed by a power of `g`. -/
theorem exists_pow_smul_eq_zero_of_liftOfLE_eq_zero {M₂ M₃ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (P : Submonoid R) (g : R) (l₂ : M →ₗ[R] M₂) (l₃ : M →ₗ[R] M₃)
    [IsLocalizedModule P l₂] [IsLocalizedModule (P ⊔ Submonoid.powers g) l₃] {x : M₂}
    (hx : liftOfLE P (P ⊔ Submonoid.powers g) le_sup_left l₂ l₃ x = 0) :
    ∃ n : ℕ, g ^ n • x = 0 := by
  obtain ⟨m, s, rfl⟩ : ∃ (m : M) (s : P), mk' l₂ m s = x := by
    obtain ⟨⟨m, s⟩, h⟩ := mk'_surjective P l₂ x
    exact ⟨m, s, h⟩
  rw [liftOfLE_mk', mk'_eq_zero'] at hx
  obtain ⟨t, ht⟩ := hx
  obtain ⟨p, hp, y, hy, hpy⟩ := Submonoid.mem_sup.mp t.2
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff y g).mp hy
  refine ⟨n, ?_⟩
  rw [← mk'_smul, mk'_eq_zero']
  refine ⟨⟨p, hp⟩, ?_⟩
  have hkill : (p * g ^ n) • m = 0 := by
    rw [hpy]
    simpa only [Submonoid.smul_def] using ht
  rw [Submonoid.smul_def, smul_smul]
  exact hkill

end Toolkit

section TripleBridge

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {f g h : R}

/-- Triple-product form of `isLocalizedModule_sup_of_powers_mul`: a localization of `M` at
`Submonoid.powers (f * g * h)` is also a localization at the double join
`Submonoid.powers f ⊔ Submonoid.powers g ⊔ Submonoid.powers h`.  This lets a consumer holding the
triple overlap module in the `powers (fᵢ * fⱼ * fₖ)` form feed it to
`exists_sub_liftOfLE_eq_of_span_eq_top`. -/
theorem isLocalizedModule_sup_sup_of_powers_mul {N : Type*} [AddCommGroup N] [Module R N]
    (l : M →ₗ[R] N) [IsLocalizedModule (Submonoid.powers (f * g * h)) l] :
    IsLocalizedModule (Submonoid.powers f ⊔ Submonoid.powers g ⊔ Submonoid.powers h) l := by
  refine IsLocalizedModule.of_exists_mul_mem (Submonoid.powers (f * g * h))
    (Submonoid.powers f ⊔ Submonoid.powers g ⊔ Submonoid.powers h) ?_ ?_ l
  · rw [Submonoid.powers_le]
    exact mul_mem (mul_mem
        (Submonoid.mem_sup_left (Submonoid.mem_sup_left (Submonoid.mem_powers f)))
        (Submonoid.mem_sup_left (Submonoid.mem_sup_right (Submonoid.mem_powers g))))
      (Submonoid.mem_sup_right (Submonoid.mem_powers h))
  · rintro ⟨z, hz⟩
    obtain ⟨w, hw, y, hy, rfl⟩ := Submonoid.mem_sup.mp hz
    obtain ⟨x, hx, y', hy', rfl⟩ := Submonoid.mem_sup.mp hw
    obtain ⟨a, rfl⟩ := (Submonoid.mem_powers_iff x f).mp hx
    obtain ⟨b, rfl⟩ := (Submonoid.mem_powers_iff y' g).mp hy'
    obtain ⟨c, rfl⟩ := (Submonoid.mem_powers_iff y h).mp hy
    exact ⟨f ^ (b + c) * g ^ (a + c) * h ^ (a + b), ⟨a + b + c, by ring⟩⟩

end TripleBridge

section FiniteCover

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι]
  {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module R (Mi i)]
  {Mij : ι → ι → Type*} [∀ i j, AddCommGroup (Mij i j)] [∀ i j, Module R (Mij i j)]
  {Mijk : ι → ι → ι → Type*} [∀ i j k, AddCommGroup (Mijk i j k)]
  [∀ i j k, Module R (Mijk i j k)]

/-- **Affine Čech `H¹` vanishing for a finite basic cover (partition-of-unity splitting).**

Let `M` be a module over a commutative ring `R` and `f : ι → R` a finite family generating the
unit ideal, so the basic opens `D(fᵢ)` cover `Spec R`.  Write `Mᵢ`, `Mᵢⱼ`, `Mᵢⱼₖ` for the
localizations of `M` at `powers fᵢ` and the joins `powers fᵢ ⊔ powers fⱼ` and
`powers fᵢ ⊔ powers fⱼ ⊔ powers fₖ` (the pairwise and triple overlaps).  Every additive Čech
`1`-cocycle `c` — a family `c i j : Mᵢⱼ` satisfying `c i j + c j k = c i k` on triple overlaps —
is a `1`-coboundary: there are `a i : Mᵢ` with `c i j = a i - a j` restricted to `Mᵢⱼ`, all
restrictions being the canonical `IsLocalizedModule.liftOfLE` maps.

The proof is the standard weighted-average argument: clear the `k`-denominator of each `c i k` at
a uniform power `N`, kill the triple defects (zero in `Mᵢⱼₖ` by the cocycle law) by a further
uniform power `Γ` of `f k`, and average against a partition of unity
`∑ k, g k * f k ^ (Γ + N) = 1`.

No alternating/normalization hypothesis on `c` is needed (the degenerate instances of the cocycle
law are part of `hcoc`). -/
theorem exists_sub_liftOfLE_eq_of_span_eq_top (f : ι → R)
    (li : ∀ i, M →ₗ[R] Mi i) (lij : ∀ i j, M →ₗ[R] Mij i j)
    (lijk : ∀ i j k, M →ₗ[R] Mijk i j k)
    [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (li i)]
    [∀ i j, IsLocalizedModule (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) (lij i j)]
    [∀ i j k, IsLocalizedModule
      (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k)) (lijk i j k)]
    (hf : Ideal.span (Set.range f) = ⊤) (c : ∀ i j, Mij i j)
    (hcoc : ∀ i j k,
      liftOfLE (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
          le_sup_left (lij i j) (lijk i j k) (c i j)
        + liftOfLE (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)
            (lij j k) (lijk i j k) (c j k)
        = liftOfLE (Submonoid.powers (f i) ⊔ Submonoid.powers (f k))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
            (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
            (lij i k) (lijk i j k) (c i k)) :
    ∃ a : ∀ i, Mi i, ∀ i j,
      c i j
        = liftOfLE (Submonoid.powers (f i))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_left
            (li i) (lij i j) (a i)
          - liftOfLE (Submonoid.powers (f j))
              (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_right
              (li j) (lij i j) (a j) := by
  classical
  -- ### Step 1: clear the `j`-denominator of every `c i j` at one uniform power `N`
  have h1 : ∀ i j, ∃ (n : ℕ) (b : Mi i),
      liftOfLE (Submonoid.powers (f i)) (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
        le_sup_left (li i) (lij i j) b = f j ^ n • c i j := fun i j =>
    exists_liftOfLE_eq_pow_smul (Submonoid.powers (f i)) (f j) (li i) (lij i j) (c i j)
  choose n₀ b₀ hb₀ using h1
  set N : ℕ := Finset.univ.sup (fun p : ι × ι => n₀ p.1 p.2) with hNdef
  have hn₀N : ∀ i j, n₀ i j ≤ N := fun i j =>
    Finset.le_sup (f := fun p : ι × ι => n₀ p.1 p.2) (Finset.mem_univ (i, j))
  have hBex : ∀ i j, ∃ b : Mi i,
      liftOfLE (Submonoid.powers (f i)) (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
        le_sup_left (li i) (lij i j) b = f j ^ N • c i j := by
    intro i j
    refine ⟨f j ^ (N - n₀ i j) • b₀ i j, ?_⟩
    rw [map_smul, hb₀ i j, smul_smul, ← pow_add, Nat.sub_add_cancel (hn₀N i j)]
  choose B hB using hBex
  -- ### Step 2: the triple defect dies in the triple localization (the cocycle law) …
  have hd0 : ∀ i j k,
      liftOfLE (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
        le_sup_left (lij i j) (lijk i j k)
        (liftOfLE (Submonoid.powers (f i))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_left
            (li i) (lij i j) (B i k)
          - liftOfLE (Submonoid.powers (f j))
              (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_right
              (li j) (lij i j) (B j k)
          - f k ^ N • c i j) = 0 := by
    intro i j k
    rw [map_sub, map_sub, map_smul,
      liftOfLE_liftOfLE (Submonoid.powers (f i))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
        le_sup_left le_sup_left (le_sup_of_le_left le_sup_left)
        (li i) (lij i j) (lijk i j k) (B i k),
      liftOfLE_liftOfLE (Submonoid.powers (f j))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f j))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
        le_sup_right le_sup_left (le_sup_of_le_left le_sup_right)
        (li j) (lij i j) (lijk i j k) (B j k),
      ← liftOfLE_liftOfLE (Submonoid.powers (f i))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f k))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
        le_sup_left (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)
        (le_sup_of_le_left le_sup_left)
        (li i) (lij i k) (lijk i j k) (B i k),
      ← liftOfLE_liftOfLE (Submonoid.powers (f j))
        (Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
        (Submonoid.powers (f i) ⊔ Submonoid.powers (f j) ⊔ Submonoid.powers (f k))
        le_sup_left (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)
        (le_sup_of_le_left le_sup_right)
        (li j) (lij j k) (lijk i j k) (B j k),
      hB i k, hB j k, map_smul, map_smul, ← hcoc i j k, smul_add]
    abel
  -- ### … hence is killed by one uniform power `Γ` of `f k`
  have hkill : ∀ i j k, ∃ n : ℕ, f k ^ n •
      (liftOfLE (Submonoid.powers (f i))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_left
          (li i) (lij i j) (B i k)
        - liftOfLE (Submonoid.powers (f j))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_right
            (li j) (lij i j) (B j k)
        - f k ^ N • c i j) = 0 := fun i j k =>
    exists_pow_smul_eq_zero_of_liftOfLE_eq_zero
      (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) (f k)
      (lij i j) (lijk i j k) (hd0 i j k)
  choose γ hγ using hkill
  set Γ : ℕ := Finset.univ.sup (fun t : ι × ι × ι => γ t.1 t.2.1 t.2.2) with hΓdef
  have hγΓ : ∀ i j k, γ i j k ≤ Γ := fun i j k =>
    Finset.le_sup (f := fun t : ι × ι × ι => γ t.1 t.2.1 t.2.2) (Finset.mem_univ (i, j, k))
  have hkey : ∀ i j k, f k ^ Γ •
      (liftOfLE (Submonoid.powers (f i))
          (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_left
          (li i) (lij i j) (B i k)
        - liftOfLE (Submonoid.powers (f j))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_right
            (li j) (lij i j) (B j k)) = f k ^ (Γ + N) • c i j := by
    intro i j k
    have hpad : f k ^ Γ •
        (liftOfLE (Submonoid.powers (f i))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_left
            (li i) (lij i j) (B i k)
          - liftOfLE (Submonoid.powers (f j))
              (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_right
              (li j) (lij i j) (B j k)
          - f k ^ N • c i j) = 0 := by
      rw [show f k ^ Γ = f k ^ (Γ - γ i j k) * f k ^ (γ i j k) by
          rw [← pow_add, Nat.sub_add_cancel (hγΓ i j k)],
        mul_smul, hγ i j k, smul_zero]
    rw [smul_sub, sub_eq_zero] at hpad
    rw [hpad, smul_smul, ← pow_add]
  -- ### Step 3: partition of unity at the exponent `Γ + N`
  obtain ⟨g, hg⟩ : ∃ g : ι → R, ∑ k, g k * f k ^ (Γ + N) = 1 := by
    refine Ideal.mem_span_range_iff_exists_fun.mp ?_
    have heq : (fun x : R => x ^ (Γ + N)) '' Set.range f
        = Set.range fun k => f k ^ (Γ + N) := by
      rw [← Set.range_comp]
      rfl
    rw [← heq, Ideal.span_pow_eq_top (Set.range f) hf (Γ + N)]
    exact Submodule.mem_top
  -- ### Step 4: the weighted average splits the cocycle
  refine ⟨fun i => ∑ k, g k • f k ^ Γ • B i k, fun i j => ?_⟩
  rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
  calc c i j = (∑ k, g k * f k ^ (Γ + N)) • c i j := by rw [hg, one_smul]
    _ = ∑ k, (g k * f k ^ (Γ + N)) • c i j := Finset.sum_smul
    _ = ∑ k,
        (liftOfLE (Submonoid.powers (f i))
            (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_left
            (li i) (lij i j) (g k • f k ^ Γ • B i k)
          - liftOfLE (Submonoid.powers (f j))
              (Submonoid.powers (f i) ⊔ Submonoid.powers (f j)) le_sup_right
              (li j) (lij i j) (g k • f k ^ Γ • B j k)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, map_smul, map_smul, map_smul, ← smul_sub, ← smul_sub, hkey i j k,
          smul_smul]

end FiniteCover

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
