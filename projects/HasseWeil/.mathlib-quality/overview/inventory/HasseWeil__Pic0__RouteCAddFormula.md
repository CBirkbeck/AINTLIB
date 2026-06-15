# Inventory: ./HasseWeil/Pic0/RouteCAddFormula.lean

**Total declarations**: 9 (7 theorems/lemmas, 1 noncomputable def, 1 def/Prop)
**Imports**: `HasseWeil.Pic0.RouteCTheoremOfSquareDiv`, `HasseWeil.Pic0.RouteCGeometric`
**No `sorry`**, **No `set_option maxHeartbeats`**

---

### `theorem sigma_kappaDivisor_picDual`

- **Type**: `{α : Isogeny E E} → α.CoordHom → Injective ch.toAlgHom → Module.Finite … → (Q : E.Point) → Curves.projectiveDivisorSum E (Curves.kappaDivisor E (α.picDual ch hinj hfin Q)) = α.picDual ch hinj hfin Q`
- **What**: The σ-bridge `σ(κ(α̂ Q)) = α̂(Q)`: the section `projectiveDivisorSum` applied to `kappaDivisor` of a dual value recovers that dual value. This is the trivial `σ ∘ κ = id` named to expose the Q2 content.
- **How**: One-line term proof via `Curves.projectiveDivisorSum_kappaDivisor E _` from the Curves library.
- **Hypotheses**: Isogeny `α : E → E` with coordinate hom, injective algebra map, and finite module structure; arbitrary point `Q`.
- **Uses from project**: `Curves.projectiveDivisorSum_kappaDivisor`, `Isogeny.picDual`, `Curves.kappaDivisor`, `Curves.projectiveDivisorSum`
- **Used by**: unused in file (referenced only in doc comments; intended for external callers)
- **Visibility**: public
- **Lines**: 128–136; proof = 1 line (term)
- **Notes**: Thin wrapper — documents reviewer Q2 content; functionally not called anywhere in this file.

---

### `noncomputable def tosPullDivisor`

- **Type**: `{α α₁ α₂ : Isogeny E E} → CoordHom/inj/fin data for each → (Q : E.Point) → Curves.ProjectiveDivisor (⟨E⟩ : Curves.SmoothPlaneCurve F)`
- **What**: Defines the pulled-back theorem-of-the-square divisor `Δ_Q := κ(ŵ(α₁⊞α₂) Q) − κ(α̂₁ Q) − κ(α̂₂ Q)`, the κ-image incarnation of `(α₁+α₂)^*((Q)−(O)) − α₁^*((Q)−(O)) − α₂^*((Q)−(O))`.
- **How**: Direct definition as the difference `kappaDivisor(α.picDual Q) - kappaDivisor(α₁.picDual Q) - kappaDivisor(α₂.picDual Q)`.
- **Hypotheses**: Three isogenies with CoordHom/injectivity/finiteness data; a point Q.
- **Uses from project**: `Curves.kappaDivisor`, `Isogeny.picDual`
- **Used by**: `sigma_tosPullDivisor`, `tos_pullback_principal_of_dual_additive_at`, `tos_pullback_principal_of_sigma_eq_zero`, `dualAddResidual_iff_sigma_vanishes`
- **Visibility**: public
- **Lines**: 144–156; body = 3 lines
- **Notes**: Key data structure — referenced by 4 other declarations in this file. No `noncomputable` surprise (uses `kappaDivisor`).

---

### `theorem sigma_tosPullDivisor`

- **Type**: `… → (Q : E.Point) → Curves.projectiveDivisorSum E (tosPullDivisor … Q) = α.picDual … Q - α₁.picDual … Q - α₂.picDual … Q`
- **What**: Computes `σ(Δ_Q) = ŵ(α₁⊞α₂)(Q) − α̂₁(Q) − α̂₂(Q)`: the projectiveDivisorSum of the pulled-back TOS divisor equals the dual-additivity defect. Combined with the next lemma, this makes Q2 exact.
- **How**: Unfolds `tosPullDivisor`, then applies `RouteCTheoremOfSquareDiv.sigma_delta` (which computes σ of a three-term kappaDivisor difference).
- **Hypotheses**: Three isogenies with CoordHom/inj/fin data; point Q.
- **Uses from project**: `tosPullDivisor`, `RouteCTheoremOfSquareDiv.sigma_delta`, `Isogeny.picDual`
- **Used by**: `tos_pullback_principal_of_sigma_eq_zero`, `dualAddResidual_iff_sigma_vanishes`
- **Visibility**: public
- **Lines**: 163–179; proof = 5 lines
- **Notes**: None.

---

### `theorem tos_pullback_principal_of_dual_additive_at`

- **Type**: `… → (Q : E.Point) → (hQ : α.picDual … Q = α₁.picDual … Q + α₂.picDual … Q) → Curves.SmoothPlaneCurve.ProjIsPrincipal (⟨E⟩) (tosPullDivisor … Q)`
- **What**: The forward half of the pulled-back theorem of the square (Silverman III.6.2(c)): whenever the dual is additive at Q (`ŵ(α₁⊞α₂)(Q) = α̂₁(Q) + α̂₂(Q)`), the divisor `Δ_Q` is principal on E. This is the genuine TOS content discharged unconditionally via Abel's κ-additivity.
- **How**: Uses `RouteCTheoremOfSquareDiv.kappaDivisor_add_linEquiv` (κ-additivity, Miller, char-free) after rewriting via `hQ`. An `abel`-proved regrouping converts the difference form to the subtraction form accepted by the linearly-equiv lemma.
- **Hypotheses**: Three isogenies with CoordHom/inj/fin data; point Q; dual-additivity at Q (`hQ`).
- **Uses from project**: `tosPullDivisor`, `RouteCTheoremOfSquareDiv.kappaDivisor_add_linEquiv`, `Isogeny.picDual`
- **Used by**: `tos_pullback_principal_of_sigma_eq_zero`
- **Visibility**: public
- **Lines**: 194–222; proof = 17 lines
- **Notes**: Core discharged step — delegates to `kappaDivisor_add_linEquiv` (Miller, char-free); the `abel` rewrite is load-bearing for grouping.

---

### `theorem tos_pullback_principal_of_sigma_eq_zero`

- **Type**: `… → (Q : E.Point) → (hσ : Curves.projectiveDivisorSum E (tosPullDivisor … Q) = 0) → Curves.SmoothPlaneCurve.ProjIsPrincipal (⟨E⟩) (tosPullDivisor … Q)`
- **What**: The pulled-back TOS divisor is principal whenever `σ(Δ_Q) = 0` (the O-vanishing of the sigma image). Combined with `sigma_tosPullDivisor`, this pins the residual: `σ(Δ_Q) = O` ⟺ `Δ_Q` principal ⟺ dual additivity at Q.
- **How**: Invokes `tos_pullback_principal_of_dual_additive_at` after recovering the dual-additivity hypothesis from `hσ`: uses `sigma_tosPullDivisor` to rewrite `hσ` as the dual-defect vanishing, then solves the algebra with `simpa`.
- **Hypotheses**: Three isogenies with CoordHom/inj/fin data; point Q; σ-vanishing `hσ`.
- **Uses from project**: `tosPullDivisor`, `sigma_tosPullDivisor`, `tos_pullback_principal_of_dual_additive_at`
- **Used by**: unused in file (intended as equivalence certifier for external use)
- **Visibility**: public
- **Lines**: 230–251; proof = 10 lines
- **Notes**: Not referenced in any proof within this file; exposed for external consumers or documentation.

---

### `def DualAddMulByIntResidual`

- **Type**: `(α α₁ α₂ : Isogeny E E) → CoordHom/inj/fin data × 3 → Prop`
  `= ∀ Q : E.Point, α.picDual … Q = α₁.picDual … Q + α₂.picDual … Q`
- **What**: Names the irreducible residual: the dual point-map `α ↦ α̂` is additive on the pair `(α₁, α₂)` at every point. This is exactly Silverman III.6.2(c) in its point-map form; by `dualAddResidual_iff_sigma_vanishes`, it is equivalent to `∀ Q, σ(Δ_Q) = O`.
- **How**: Plain `Prop` definition (no tactic proof).
- **Hypotheses**: Three isogenies, CoordHom/inj/fin data for each.
- **Uses from project**: `Isogeny.picDual`
- **Used by**: `dualAddResidual_iff_sigma_vanishes`, `picDual_add_of_dualAddResidual`, `htrace_dual_of_dualAddMulByInt_residual`
- **Visibility**: public
- **Lines**: 267–276; body = 2 lines
- **Notes**: Key API — used by 3 declarations in this file. Acts as the named "open sorry" / residual predicate for the theorem of the square.

---

### `theorem dualAddResidual_iff_sigma_vanishes`

- **Type**: `… → DualAddMulByIntResidual α α₁ α₂ … ↔ (∀ Q : E.Point, Curves.projectiveDivisorSum E (tosPullDivisor … Q) = 0)`
- **What**: The named residual `DualAddMulByIntResidual` is exactly the statement that the σ-image of the pulled-back TOS divisor vanishes at every Q. Certifies the Q2 equivalence: dual additivity ⟺ `σ(Δ_Q) = O`.
- **How**: `forall_congr'` reduces to pointwise equivalence; `sigma_tosPullDivisor` rewrites the σ-form; both directions are algebra with `abel`/`simpa`.
- **Hypotheses**: Three isogenies with CoordHom/inj/fin data.
- **Uses from project**: `DualAddMulByIntResidual`, `sigma_tosPullDivisor`, `tosPullDivisor`
- **Used by**: unused in file (only referenced in doc comments)
- **Visibility**: public
- **Lines**: 282–303; proof = 11 lines
- **Notes**: Not called in any proof in this file; purely documentation/external API for the Q2 equivalence.

---

### `theorem picDual_add_of_dualAddResidual`

- **Type**: `… → (hres : DualAddMulByIntResidual α α₁ α₂ …) → α.picDual … = α₁.picDual … + α₂.picDual …`
- **What**: Converts the pointwise residual `DualAddMulByIntResidual` to the `AddMonoidHom` equality `picDual α = picDual α₁ + picDual α₂` (`hadd`). This is the consumer hand-off to `RouteCTheoremOfSquareDiv.htrace_dual_of_picDual_add`.
- **How**: `ext Q` reduces to the pointwise form, then applies `hres Q` directly.
- **Hypotheses**: Three isogenies with CoordHom/inj/fin data; `DualAddMulByIntResidual` hypothesis.
- **Uses from project**: `DualAddMulByIntResidual`, `Isogeny.picDual`
- **Used by**: `htrace_dual_of_dualAddMulByInt_residual`
- **Visibility**: public
- **Lines**: 311–324; proof = 3 lines
- **Notes**: Very short proof — ext + apply. Critical bridge between the Prop-form and the AddMonoidHom equality.

---

### `theorem htrace_dual_of_dualAddMulByInt_residual`

- **Type**: `(hq : 2 ≤ Fintype.card K) → (r s : ℤ) → hr hs hrK hsK → (V : Isogeny …) → CoordHom/inj/fin × 3 → (h_sum_trace) → (hdual₁) → (hdual₂) → (hres : DualAddMulByIntResidual …) → (genuineIsogSmulSub W r s …).toAddMonoidHom + (…).picDual … = (mulByInt W.toAffine (r * isogTrace … - 2 * s)).toAddMonoidHom`
- **What**: The Route-C drop-in: from the scalar pulled-back theorem-of-the-square residual and three shipped seeds (trace relation `π + V = [t]`, `(rπ)̂ = rV`, `[−s]̂ = [−s]`), derives the exact Frobenius trace relation `htrace_dual` (`α + α̂ = [rt − 2s]`) consumed by `RouteCGeometric.degree_eq_N_via_picDual_geometric_hpicval_discharged`. This is the main payoff of the file.
- **How**: First establishes `hbeta` (the `r·π − s` shape) by `rw [genuineIsogSmulSub_toAddMonoidHom]` + `simp` + `neg_smul`. Then calls `RouteCTheoremOfSquareDiv.htrace_dual_of_picDual_add`, passing `picDual_add_of_dualAddResidual` to supply the converted `hadd`.
- **Hypotheses**: `2 ≤ #K` (finite field); `r, s ≠ 0` in ℤ and as field elements; Verdoux isogeny `V`; CoordHom/inj/fin data for three isogenies; trace sum relation `h_sum_trace`; dual seeds `hdual₁, hdual₂`; the theorem-of-the-square residual `hres`.
- **Uses from project**: `DualAddMulByIntResidual`, `picDual_add_of_dualAddResidual`, `genuineIsogSmulSub`, `genuineIsogSmulSub_toAddMonoidHom`, `frobeniusIsog`, `mulByInt`, `isogTrace`, `isogOneSub_negFrobenius`, `RouteCTheoremOfSquareDiv.htrace_dual_of_picDual_add`, `Isogeny.zsmul_apply`, `mulByInt_apply`
- **Used by**: unused in file (the external payoff for `RouteCGeometric`)
- **Visibility**: public
- **Lines**: 365–408; total declaration = 44 lines; proof = 15 lines
- **Notes**: Longest declaration in the file (44 lines total). Not called within this file; intended to be consumed by `RouteCGeometric.degree_eq_N_via_picDual_geometric_hpicval_discharged`. No sorry, no heartbeat override.

---

## Summary

| Stat | Value |
|---|---|
| Total declarations | 9 |
| Theorems/lemmas | 7 |
| Noncomputable defs | 1 (`tosPullDivisor`) |
| Prop defs | 1 (`DualAddMulByIntResidual`) |
| Instances | 0 |
| Sorries | 0 |
| `set_option maxHeartbeats` | 0 |
| Long proofs (>30 lines) | 0 |

**Key API (used by 3+ in file)**: `tosPullDivisor` (4 uses), `DualAddMulByIntResidual` (3 uses).

**Declarations unused in this file**: `sigma_kappaDivisor_picDual`, `tos_pullback_principal_of_sigma_eq_zero`, `dualAddResidual_iff_sigma_vanishes`, `htrace_dual_of_dualAddMulByInt_residual`.

**Notable machinery**: The entire file is axiom-clean and characteristic-free over any field; it uses `RouteCTheoremOfSquareDiv.kappaDivisor_add_linEquiv` (Miller / Abel, char-free) and `sigma_delta` as the core discharged steps. The file packages the precise irreducible residual for Silverman III.6.2(c) dual additivity and wires it into the Route-C `htrace_dual` consumer. No `E × E` API is used — everything works directly on `E` via κ-divisors.
