# Inventory: PadicLFunctions/Measure/Basic.lean

File path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/Measure/Basic.lean`

Module: p-adic measures on a compact space (Rodrigues Jacinto–Williams §3.2). Defines `ℤ_[p]`-valued measures as `ℤ_[p]`-linear functionals on `C(X, ℤ_[p])`, with automatic boundedness/continuity, density of locally constant functions, and an extensionality principle.

---

### instance (anonymous) `NeZero (p ^ n)`
- Type: `instance (n : ℕ) : NeZero (p ^ n)`
- What: For a prime `p`, the power `p ^ n` is nonzero (registered as a typeclass instance).
- How: Anonymous constructor wrapping `pow_ne_zero n hp.out.ne_zero` — `p` is nonzero because it is prime, so any power is nonzero.
- Hypotheses: `p : ℕ` with `[Fact p.Prime]`; `n : ℕ` arbitrary.
- Uses from project: []
- Used by: unused in file (provides an ambient instance consumed implicitly by `ZMod (p ^ k)` / `ZMod (p ^ n)` machinery, e.g. in `isOpen_toZModPow_fiber`, `exists_locallyConstant_norm_sub_le`, `LocallyConstant.exists_eq_comp_toZModPow`)
- Visibility: public
- Lines: 41 (proof: inline, 1 line)
- Notes: none

### abbrev `PadicMeasure`
- Type: `abbrev PadicMeasure (X : Type*) [TopologicalSpace X] := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`
- What: The space of `ℤ_[p]`-valued p-adic measures on a topological space `X`, defined as the `ℤ_[p]`-linear functionals on continuous `ℤ_[p]`-valued functions; over `ℤ_[p]` linearity already forces boundedness/continuity so this coincides with the continuous dual of the source.
- How: A type abbreviation for the linear-maps type `C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`; no proof.
- Hypotheses: `p` prime (ambient); `X` a topological space.
- Uses from project: []
- Used by: `dirac`, `pushforward`, `norm_apply_le`, `continuous`, `ext_locallyConstant` (and all lemmas mentioning measures)
- Visibility: public
- Lines: 52–53 (no proof)
- Notes: none

### def `dirac`
- Type: `def dirac (x : X) : PadicMeasure p X` (fields `toFun f := f x`, `map_add'`, `map_smul'`)
- What: The Dirac measure at a point `x`, i.e. the evaluation functional `φ ↦ φ x` (RJW Ex. 3.7).
- How: Structure literal giving the linear map; additivity and `ℤ_[p]`-linearity of evaluation both hold by `rfl`.
- Hypotheses: `x : X`; `X` a topological space.
- Uses from project: [`PadicMeasure`]
- Used by: `dirac_apply`, `pushforward_dirac`
- Visibility: public
- Lines: 64–67 (proof: `rfl`/`rfl`)
- Notes: none

### lemma `dirac_apply`
- Type: `lemma dirac_apply (x : X) (f : C(X, ℤ_[p])) : dirac p x f = f x` `@[simp]`
- What: Evaluating the Dirac measure at `x` on a function `f` returns `f x`.
- How: `rfl` — unfolds the definition of `dirac`.
- Hypotheses: `x : X`, `f` continuous `ℤ_[p]`-valued.
- Uses from project: [`dirac`]
- Used by: unused in file
- Visibility: public
- Lines: 69–70 (proof: `rfl`)
- Notes: none

### def `compRight`
- Type: `def compRight (m : C(X, Y)) : C(Y, ℤ_[p]) →ₗ[ℤ_[p]] C(X, ℤ_[p])` (fields `toFun f := f.comp m`, `map_add'`, `map_smul'`)
- What: Precomposition with a continuous map `m : X → Y`, as a `ℤ_[p]`-linear map sending `f : C(Y, ℤ_[p])` to `f ∘ m`; auxiliary for `pushforward`.
- How: Structure literal; additivity and scalar-compatibility proved by `ext; simp` (pointwise on the composite).
- Hypotheses: `m : C(X, Y)`; `X`, `Y` topological spaces.
- Uses from project: []
- Used by: `compRight_apply`, `pushforward`
- Visibility: public
- Lines: 74–77 (proof: `ext; simp` x2)
- Notes: none

### lemma `compRight_apply`
- Type: `lemma compRight_apply (m : C(X, Y)) (f : C(Y, ℤ_[p])) : compRight p m f = f.comp m` `@[simp]`
- What: The precomposition map `compRight p m` sends `f` to `f.comp m`.
- How: `rfl` — unfolds `compRight`.
- Hypotheses: `m : C(X, Y)`, `f : C(Y, ℤ_[p])`.
- Uses from project: [`compRight`]
- Used by: unused in file
- Visibility: public
- Lines: 79–80 (proof: `rfl`)
- Notes: none

### def `pushforward`
- Type: `def pushforward (m : C(X, Y)) : PadicMeasure p X →ₗ[ℤ_[p]] PadicMeasure p Y` (field `toFun μ := μ.comp (compRight p m)`, `map_add'`, `map_smul'`)
- What: The pushforward of a measure along a continuous map `m`, defined by `(pushforward m μ) f = μ (f ∘ m)`; later specialises to the `σ_a`, `φ` operators and the embedding `Λ(ℤ_p^×) → Λ(ℤ_p)`.
- How: Structure literal composing the functional `μ` with `compRight p m`; linearity in `μ` holds by `rfl`/`rfl`.
- Hypotheses: `m : C(X, Y)`; `X`, `Y` topological spaces.
- Uses from project: [`PadicMeasure`, `compRight`]
- Used by: `pushforward_apply`, `pushforward_dirac`
- Visibility: public
- Lines: 85–88 (proof: `rfl`/`rfl`)
- Notes: none

### lemma `pushforward_apply`
- Type: `lemma pushforward_apply (m : C(X, Y)) (μ : PadicMeasure p X) (f : C(Y, ℤ_[p])) : pushforward p m μ f = μ (f.comp m)` `@[simp]`
- What: Evaluating a pushed-forward measure on `f` equals evaluating the original measure on `f ∘ m`.
- How: `rfl` — unfolds `pushforward` and `compRight`.
- Hypotheses: `m`, `μ`, `f` as stated.
- Uses from project: [`pushforward`, `PadicMeasure`]
- Used by: unused in file
- Visibility: public
- Lines: 90–92 (proof: `rfl`)
- Notes: none

### lemma `pushforward_dirac`
- Type: `lemma pushforward_dirac (m : C(X, Y)) (x : X) : pushforward p m (dirac p x) = dirac p (m x)` `@[simp]`
- What: The pushforward of a Dirac measure at `x` along `m` is the Dirac measure at `m x` (naturality of Dirac).
- How: `rfl` — both sides evaluate `f ↦ f (m x)` definitionally.
- Hypotheses: `m : C(X, Y)`, `x : X`.
- Uses from project: [`pushforward`, `dirac`]
- Used by: unused in file
- Visibility: public
- Lines: 94–96 (proof: `rfl`)
- Notes: none

### theorem `norm_apply_le`
- Type: `theorem norm_apply_le (μ : PadicMeasure p X) (f : C(X, ℤ_[p])) : ‖μ f‖ ≤ ‖f‖` (requires `[CompactSpace X]`)
- What: Every `ℤ_[p]`-linear functional on `C(X, ℤ_[p])` over a compact `X` is bounded by the sup-norm of its argument (norm ≤ 1 operator), establishing automatic boundedness of measures (RJW Def. 3.6 footnote).
- How: Case split on `X` empty / `f = 0` (trivial). Otherwise pick a sup-norm maximiser `x₀` via `isCompact_univ.exists_isMaxOn` applied to `‖f‖` continuous; set `n = (f x₀).valuation` so `‖f‖ = p^(-n)` (`PadicInt.norm_eq_zpow_neg_valuation`); construct `g : C(X, ℤ_[p])` with `g x = f x / p^n` (norm ≤ 1 via `Padic.norm_p_pow` and `div_le_one`), prove `f = p^n • g`, then `‖μ f‖ = ‖p^n‖·‖μ g‖ ≤ p^(-n)·1 = ‖f‖` via `PadicInt.norm_p_pow` and `PadicInt.norm_le_one`.
- Hypotheses: `X` compact; `μ` a `ℤ_[p]`-linear functional; `f` continuous `ℤ_[p]`-valued.
- Uses from project: [`PadicMeasure`]
- Used by: `continuous`, `ext_locallyConstant`
- Visibility: public
- Lines: 109–149 (proof ≈ 41 lines)
- Notes: long(30-50)

### theorem `continuous`
- Type: `theorem continuous (μ : PadicMeasure p X) : Continuous μ` (requires `[CompactSpace X]`)
- What: Every p-adic measure (linear functional) on a compact `X` is continuous, matching the source's "measures are continuous (equivalently bounded)".
- How: Shows `μ` is `LipschitzWith 1` via `LipschitzWith.of_dist_le_mul`, using `dist_eq_norm`, `map_sub` and the bound `norm_apply_le p μ (f - g)`; Lipschitz implies continuous.
- Hypotheses: `X` compact; `μ` a measure.
- Uses from project: [`PadicMeasure`, `norm_apply_le`]
- Used by: unused in file
- Visibility: public
- Lines: 153–156 (proof ≈ 3 lines)
- Notes: none

### lemma `isOpen_toZModPow_fiber`
- Type: `lemma isOpen_toZModPow_fiber (k : ℕ) (a : ZMod (p ^ k)) : IsOpen {z : ℤ_[p] | PadicInt.toZModPow k z = a}` (requires `[CompactSpace X]` in scope, unused)
- What: The fiber (residue disc) of the reduction `toZModPow k : ℤ_[p] → ZMod (p^k)` over a value `a` is open in `ℤ_[p]`; the workhorse clopen-ness for density and the ψ-operator digit shift.
- How: Via `Metric.isOpen_iff`: around a point `z` in the fiber, take radius `p^(-k)`; for `y` in that ball, `toZModPow k (y - z) = 0` because `‖y - z‖ ≤ p^(-k)` lands in `ker (toZModPow k)` (`PadicInt.ker_toZModPow`, `PadicInt.norm_le_pow_iff_mem_span_pow`), so `toZModPow k y = toZModPow k z = a`.
- Hypotheses: `k : ℕ`, `a : ZMod (p^k)`.
- Uses from project: []
- Used by: `exists_locallyConstant_norm_sub_le`, `isLocallyConstant_toZModPow_val`, `LocallyConstant.exists_eq_comp_toZModPow`
- Visibility: public
- Lines: 160–170 (proof ≈ 11 lines)
- Notes: none

### lemma `isLocallyConstant_toZModPow_val`
- Type: `lemma isLocallyConstant_toZModPow_val (k : ℕ) : IsLocallyConstant fun x : ℤ_[p] => (((PadicInt.toZModPow k x).val : ℕ) : ℤ_[p])`
- What: The canonical-digit lift `x ↦ [x mod p^k]` from `ℤ_[p]` to `ℤ_[p]` (reduce mod `p^k`, take the natural representative, embed back) is locally constant, hence continuous.
- How: `IsLocallyConstant.comp` of the lift function over the locally constant map `toZModPow k`; local constancy of `toZModPow k` is shown by rewriting each preimage as a union of singleton-fibers (`Set.biUnion_preimage_singleton`) and applying `isOpen_toZModPow_fiber`.
- Hypotheses: `k : ℕ`.
- Uses from project: [`isOpen_toZModPow_fiber`]
- Used by: unused in file
- Visibility: public
- Lines: 174–179 (proof ≈ 4 lines)
- Notes: none

### theorem `exists_locallyConstant_norm_sub_le`
- Type: `theorem exists_locallyConstant_norm_sub_le (f : C(X, ℤ_[p])) {ε : ℝ} (hε : 0 < ε) : ∃ g : LocallyConstant X ℤ_[p], ‖f - (g : C(X, ℤ_[p]))‖ ≤ ε` (requires `[CompactSpace X]`)
- What: Density of locally constant functions — any continuous `f : X → ℤ_[p]` on a compact space is uniformly `ε`-approximated by a locally constant function (RJW Rem. 3.8).
- How: Choose `k` with `p^(-k) < ε` (`PadicInt.exists_pow_neg_lt`); set `q x = toZModPow k (f x)`, locally constant since fibers are open (`isOpen_toZModPow_fiber` pulled back along `f` continuous, via `Set.biUnion_preimage_singleton`); take `g x = (q x).val` and bound `‖f x - (q x).val‖ ≤ p^(-k) ≤ ε` using `toZModPow k ((q x).val) = q x` (`ZMod.natCast_rightInverse`) and `PadicInt.norm_le_pow_iff_mem_span_pow` / `ker_toZModPow`.
- Hypotheses: `X` compact; `f` continuous; `ε > 0`.
- Uses from project: [`isOpen_toZModPow_fiber`]
- Used by: `ext_locallyConstant`
- Visibility: public
- Lines: 189–208 (proof ≈ 20 lines)
- Notes: none

### theorem `LocallyConstant.exists_eq_comp_toZModPow` (root namespace)
- Type: `theorem _root_.LocallyConstant.exists_eq_comp_toZModPow {α : Type*} (Φ : LocallyConstant ℤ_[p] α) : ∃ (n : ℕ) (g : ZMod (p ^ n) → α), ⇑Φ = g ∘ (PadicInt.toZModPow n)` (declared inside `section compact`, so `[CompactSpace X]` is in scope but unused)
- What: Any locally constant function on `ℤ_[p]` (valued in an arbitrary type) factors through a finite quotient `toZModPow n`, i.e. local constancy is uniform on the compact `ℤ_[p]`.
- How: For each `x` find `nx` with `toZModPow (nx) y = toZModPow (nx) x ⟹ Φ y = Φ x` (open fiber `Φ.isLocallyConstant.isOpen_fiber` contains a ball of radius `ε`, choose `nx` with `p^(-nx) < ε`); the fibers cover the compact `ℤ_[p]`, extract a finite subcover `t` via `IsCompact.elim_nhds_subcover`, set `n = t.sup nx`; the key `hconst` step shows `toZModPow n y = toZModPow n x ⟹ Φ y = Φ x` using the ultrametric inequality `IsUltrametricDist.norm_add_le_max` to compare `y, x` to a covering center `xi` at level `nx xi ≤ n` (`Finset.le_sup`, `zpow_le_zpow_right₀`); then `g a = Φ ((a.val : ℤ_[p]))` works via `ZMod.natCast_rightInverse`.
- Hypotheses: `α` any type; `Φ` locally constant on `ℤ_[p]`. (Implicitly uses compactness of `ℤ_[p]` and its ultrametric structure.)
- Uses from project: [`isOpen_toZModPow_fiber`]
- Used by: unused in file
- Visibility: public (extends `LocallyConstant` namespace via `_root_`)
- Lines: 213–261 (proof ≈ 47 lines)
- Notes: long(30-50); uses `classical`

### theorem `ext_locallyConstant`
- Type: `theorem ext_locallyConstant {μ ν : PadicMeasure p X} (h : ∀ g : LocallyConstant X ℤ_[p], μ (g : C(X, ℤ_[p])) = ν (g : C(X, ℤ_[p]))) : μ = ν` (requires `[CompactSpace X]`)
- What: A p-adic measure on a compact `X` is determined by its values on locally constant functions; agreement there forces global equality (injectivity half of RJW Eq. (3.1), `ℳ ≅ ℳ^lc`).
- How: `LinearMap.ext` reduces to `μ f = ν f` for each `f`; uses `eq_of_forall_dist_le` to bound `dist (μ f) (ν f)` for every `ε > 0`. Approximate `f` by a locally constant `g` (`exists_locallyConstant_norm_sub_le`); since `μ g = ν g`, the difference `μ f - ν f` equals `μ(f-g) - ν(f-g)`, bounded by `max ‖μ(f-g)‖ ‖ν(f-g)‖` (`IsUltrametricDist.norm_add_le_max`) ≤ `‖f-g‖` (via `norm_apply_le` for both `μ`, `ν`) ≤ `ε`.
- Hypotheses: `X` compact; `μ`, `ν` measures agreeing on all locally constant functions.
- Uses from project: [`PadicMeasure`, `exists_locallyConstant_norm_sub_le`, `norm_apply_le`]
- Used by: unused in file
- Visibility: public
- Lines: 267–282 (proof ≈ 13 lines)
- Notes: none

---

## File Summary

- **Total declarations: 14** — defs: 3 (`dirac`, `compRight`, `pushforward`); lemmas+theorems: 10 (`dirac_apply`, `compRight_apply`, `pushforward_apply`, `pushforward_dirac`, `norm_apply_le`, `continuous`, `isOpen_toZModPow_fiber`, `isLocallyConstant_toZModPow_val`, `exists_locallyConstant_norm_sub_le`, `LocallyConstant.exists_eq_comp_toZModPow`, `ext_locallyConstant` — that is 11); instances: 1 (anonymous `NeZero (p ^ n)`); abbrev: 1 (`PadicMeasure`). (3 defs + 11 lemmas/theorems + 1 instance + 1 abbrev = 16 named items incl. abbrev & instance; "declaration" count of def/lemma/theorem/instance/abbrev = 16.)
- **Key API (used by ≥3 in file):** `isOpen_toZModPow_fiber` (used by `isLocallyConstant_toZModPow_val`, `exists_locallyConstant_norm_sub_le`, `LocallyConstant.exists_eq_comp_toZModPow`); `PadicMeasure` (used by `dirac`, `pushforward`, `norm_apply_le`, `continuous`, `ext_locallyConstant`, `pushforward_apply`); `norm_apply_le` (used by `continuous`, `ext_locallyConstant` — 2, just under threshold).
- **Unused in file (no in-file consumer):** the anonymous `NeZero (p ^ n)` instance, `dirac_apply`, `compRight_apply`, `pushforward_apply`, `pushforward_dirac`, `continuous`, `isLocallyConstant_toZModPow_val`, `LocallyConstant.exists_eq_comp_toZModPow`, `ext_locallyConstant` (these are public API for downstream measure/Iwasawa files).
- **Decls with `sorry`:** none.
- **`set_option`:** none.
- **Proofs >50 lines:** 0.
- **Proofs 30–50 lines:** 2 — `norm_apply_le` (≈41), `LocallyConstant.exists_eq_comp_toZModPow` (≈47).
