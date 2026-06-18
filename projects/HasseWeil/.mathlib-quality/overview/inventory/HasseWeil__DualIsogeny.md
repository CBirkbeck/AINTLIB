# Inventory: ./HasseWeil/DualIsogeny.lean

**File**: `HasseWeil/DualIsogeny.lean`
**Import**: `HasseWeil.Endomorphism`
**Total lines**: 403
**Sections**: `DualIsogeny`, `DualAdditivity`, `TraceConnection`, `DualHom`

---

## Declaration Inventory

### `def IsDualOf`

- **Type**: `(β α : Isogeny E E) : Prop := β.comp α = mulByInt E α.degree ∧ α.comp β = mulByInt E α.degree`
- **What**: Defines the dual-isogeny relation: `β` is a dual of `α` if composing in both orders yields the multiplication-by-degree map `[deg α]`.
- **How**: Pure definitional unfolding of two composition equalities; no proof content.
- **Hypotheses**: `E : Affine F`, `[E.IsElliptic]`.
- **Uses from project**: `mulByInt` (Basic.lean), `Isogeny.comp` (Basic.lean).
- **Used by**: `exists_dual_of_construction`, `exists_dual_of_constructor`, `exists_dual_iff_constructor`, `exists_dual`, `isogDual_comp_self_of_witness`, `self_comp_isogDual_of_witness`, `degree_dual_of_witness`, `isogDual_spec`, `isogDual_unique`, `isogDual_isogDual`, `isogDual_mulByInt_of_comp`.
- **Visibility**: public
- **Lines**: 49–50, definitional (1 line body)
- **Notes**: None.

---

### `theorem exists_dual_of_construction`

- **Type**: `(α dual : Isogeny E E) (h_dual : IsDualOf E dual α) (h_unique : ∀ β, IsDualOf E β α → β = dual) : ∃! β : Isogeny E E, IsDualOf E β α`
- **What**: Packages a given dual witness and its uniqueness proof into the `∃!` statement for the dual of `α`. Silverman III.6.1 parametric form.
- **How**: Trivial term-mode proof `⟨dual, h_dual, h_unique⟩` using the `∃!` constructor.
- **Hypotheses**: Explicit dual `dual` with `IsDualOf E dual α` and a uniqueness proof.
- **Uses from project**: `IsDualOf`.
- **Used by**: `exists_dual_of_constructor`, `exists_dual_iff_constructor`.
- **Visibility**: public
- **Lines**: 82–88, proof length 1 line
- **Notes**: None.

---

### `theorem exists_dual_of_constructor`

- **Type**: `(dualOf : Isogeny E E → Isogeny E E) (h_dual : ∀ α, IsDualOf E (dualOf α) α) (h_unique : ∀ α β, IsDualOf E β α → β = dualOf α) (α : Isogeny E E) : ∃! β : Isogeny E E, IsDualOf E β α`
- **What**: Wholesale parametric form: a universal constructor plus uniqueness gives `∃! dual` for every `α` at once, by applying `exists_dual_of_construction` at `α`.
- **How**: One-line call to `exists_dual_of_construction E α (dualOf α) (h_dual α) (h_unique α)`.
- **Hypotheses**: A function `dualOf` satisfying `IsDualOf` universally, plus universal uniqueness.
- **Uses from project**: `IsDualOf`, `exists_dual_of_construction`.
- **Used by**: `exists_dual_iff_constructor`.
- **Visibility**: public
- **Lines**: 94–100, proof length 1 line
- **Notes**: None.

---

### `theorem exists_dual_iff_constructor`

- **Type**: `(∀ α : Isogeny E E, ∃! β : Isogeny E E, IsDualOf E β α) ↔ ∃ dualOf : Isogeny E E → Isogeny E E, (∀ α, IsDualOf E (dualOf α) α) ∧ (∀ α β, IsDualOf E β α → β = dualOf α)`
- **What**: A meta-identity characterising dual existence: the universal `∃!` statement is logically equivalent to the existence of a constructor-plus-uniqueness pair. Pure scaffold lemma.
- **How**: Forward direction extracts `choose` and `choose_spec`; backward direction applies `exists_dual_of_constructor`.
- **Hypotheses**: None beyond the elliptic curve context.
- **Uses from project**: `IsDualOf`, `exists_dual_of_constructor`.
- **Used by**: unused in file (infrastructure lemma for Route A/B connection).
- **Visibility**: public
- **Lines**: 106–114, proof length ~5 lines
- **Notes**: Dead code within this file; provided for Route A/B discharge wiring.

---

### `theorem exists_dual`

- **Type**: `(α : Isogeny E E) : ∃! β : Isogeny E E, IsDualOf E β α`
- **What**: Silverman III.6.1: for every endomorphism `α` of an elliptic curve, there exists a unique `β` with `β ∘ α = [deg α]` and `α ∘ β = [deg α]`.
- **How**: `sorry` — genuinely blocked on ~2000 lines of upstream infrastructure (Silverman III.4.15/16/17 kernel theory + quotient curve, or Pic⁰(E) ≅ E correspondence).
- **Hypotheses**: None beyond elliptic curve.
- **Uses from project**: `IsDualOf`.
- **Used by**: `isogDual`, `isogDual_spec`, `isogDual_unique`.
- **Visibility**: public
- **Lines**: 141–142, proof = `sorry`
- **Notes**: **sorry**. Keystone sorry gating all of `isogDual` and its downstream lemmas. Designated T-III-6-001 in ticket system.

---

### `theorem isogDual_comp_self_of_witness`

- **Type**: `(α dual : Isogeny E E) (h_dual : IsDualOf E dual α) : dual.comp α = mulByInt E α.degree`
- **What**: Witness-parametric first composition identity: given an explicit dual witness, extract `dual ∘ α = [deg α]`. Does not depend on `exists_dual`.
- **How**: Immediate from `h_dual.1` (first component of `IsDualOf`).
- **Hypotheses**: Explicit dual witness satisfying `IsDualOf`.
- **Uses from project**: `IsDualOf`, `mulByInt`.
- **Used by**: unused in file (called by external files).
- **Visibility**: public
- **Lines**: 154–157, proof length 1 line
- **Notes**: Witness-parametric design avoids the `exists_dual` sorry.

---

### `theorem self_comp_isogDual_of_witness`

- **Type**: `(α dual : Isogeny E E) (h_dual : IsDualOf E dual α) : α.comp dual = mulByInt E α.degree`
- **What**: Witness-parametric second composition identity: `α ∘ dual = [deg α]`. Does not depend on `exists_dual`.
- **How**: Immediate from `h_dual.2`.
- **Hypotheses**: Explicit dual witness satisfying `IsDualOf`.
- **Uses from project**: `IsDualOf`, `mulByInt`.
- **Used by**: unused in file (called by external files).
- **Visibility**: public
- **Lines**: 159–162, proof length 1 line
- **Notes**: Witness-parametric design.

---

### `theorem degree_dual_of_witness`

- **Type**: `(α dual : Isogeny E E) (hα : 0 < α.degree) (h_dual : IsDualOf E dual α) : dual.degree = α.degree`
- **What**: Witness-parametric `deg(dual) = deg α` for nonzero `α`. Does not depend on `exists_dual`.
- **How**: From `dual.comp α = [deg α]`, takes degrees via `Isogeny.comp_degree`, rewrites using `mulByInt_degree`, uses `Nat.eq_of_mul_eq_mul_left` to cancel `α.degree` from `deg(dual) · deg(α) = deg(α)²`.
- **Hypotheses**: `0 < α.degree` (i.e. α nonzero), explicit dual witness.
- **Uses from project**: `IsDualOf`, `Isogeny.comp_degree` (Basic.lean), `mulByInt_degree` (Basic.lean).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 167–179, proof length ~12 lines
- **Notes**: Mirrors `degree_isogDual` but witness-parametric (no `exists_dual` dependency).

---

### `noncomputable def isogDual`

- **Type**: `(α : Isogeny E E) : Isogeny E E`
- **What**: The dual isogeny `α̂` of `α`, defined via classical choice from `exists_dual`. Reference: Silverman III.6.1.
- **How**: `(exists_dual E α).choose` — classical choice from the `∃!` statement.
- **Hypotheses**: Elliptic curve context; depends transitively on `exists_dual` sorry.
- **Uses from project**: `exists_dual`.
- **Used by**: `isogDual_spec`, `isogDual_comp_self`, `self_comp_isogDual`, `isogDual_unique`, `degree_isogDual`, `isogDual_isogDual`, `isogDual_add_of_sum_dual`, `isogTrace_eq_dual`, `isogDual_comp_self_apply`, `isogDual_mulByInt_of_comp`.
- **Visibility**: public
- **Lines**: 185–186, body length 1 line
- **Notes**: Carries `sorry` transitively via `exists_dual`.

---

### `theorem isogDual_spec`

- **Type**: `(α : Isogeny E E) : IsDualOf E (isogDual E α) α`
- **What**: The defining property of `isogDual`: it satisfies both composition identities.
- **How**: `(exists_dual E α).choose_spec.1` — the first component of the `∃!` spec.
- **Hypotheses**: Depends on `exists_dual` sorry.
- **Uses from project**: `IsDualOf`, `isogDual`, `exists_dual`.
- **Used by**: `isogDual_comp_self`, `self_comp_isogDual`.
- **Visibility**: public
- **Lines**: 189–190, proof length 1 line
- **Notes**: Carries `sorry` via `exists_dual`.

---

### `theorem isogDual_comp_self`

- **Type**: `(α : Isogeny E E) : (isogDual E α).comp α = mulByInt E α.degree`
- **What**: Silverman III.6.1: `α̂ ∘ α = [deg α]`.
- **How**: `(isogDual_spec E α).1`.
- **Hypotheses**: Depends on `exists_dual` sorry.
- **Uses from project**: `isogDual_spec`, `isogDual`, `mulByInt`.
- **Used by**: `degree_isogDual`, `isogDual_isogDual`, `isogDual_comp_self_apply`.
- **Visibility**: public
- **Lines**: 193–195, proof length 1 line
- **Notes**: Carries `sorry` via `exists_dual`.

---

### `theorem self_comp_isogDual`

- **Type**: `(α : Isogeny E E) : α.comp (isogDual E α) = mulByInt E α.degree`
- **What**: Silverman III.6.1: `α ∘ α̂ = [deg α]`.
- **How**: `(isogDual_spec E α).2`.
- **Hypotheses**: Depends on `exists_dual` sorry.
- **Uses from project**: `isogDual_spec`, `isogDual`, `mulByInt`.
- **Used by**: `isogDual_isogDual`.
- **Visibility**: public
- **Lines**: 198–200, proof length 1 line
- **Notes**: Carries `sorry` via `exists_dual`.

---

### `theorem isogDual_unique`

- **Type**: `(α β : Isogeny E E) (h : IsDualOf E β α) : β = isogDual E α`
- **What**: Uniqueness of the dual: any `β` satisfying `IsDualOf E β α` equals `isogDual E α`.
- **How**: `(exists_dual E α).choose_spec.2 β h` — the uniqueness clause of the `∃!` statement.
- **Hypotheses**: `IsDualOf E β α`; depends on `exists_dual` sorry.
- **Uses from project**: `IsDualOf`, `isogDual`, `exists_dual`.
- **Used by**: `isogDual_isogDual`, `isogDual_mulByInt_of_comp`.
- **Visibility**: public
- **Lines**: 204–206, proof length 1 line
- **Notes**: Carries `sorry` via `exists_dual`.

---

### `theorem degree_isogDual`

- **Type**: `(α : Isogeny E E) (hα : 0 < α.degree) : (isogDual E α).degree = α.degree`
- **What**: Silverman III.6.2(a): `deg(α̂) = deg(α)` for nonzero `α`.
- **How**: From `isogDual_comp_self`, computes degrees via `Isogeny.comp_degree`, rewrites using `mulByInt_degree`, then uses `Nat.eq_of_mul_eq_mul_left` to cancel the `α.degree` factor from `deg(α̂) · deg(α) = deg(α)²`.
- **Hypotheses**: `0 < α.degree`; depends on `exists_dual` sorry via `isogDual`.
- **Uses from project**: `isogDual_comp_self`, `Isogeny.comp_degree` (Basic.lean), `mulByInt_degree` (Basic.lean), `isogDual`.
- **Used by**: `isogDual_isogDual`.
- **Visibility**: public
- **Lines**: 212–222, proof length ~10 lines
- **Notes**: Carries `sorry` via `exists_dual`. Proof structure identical to `degree_dual_of_witness`.

---

### `theorem isogDual_isogDual`

- **Type**: `(α : Isogeny E E) (hα : 0 < α.degree) : isogDual E (isogDual E α) = α`
- **What**: Silverman III.6.2(b): the dual of the dual is the original endomorphism (for nonzero `α`).
- **How**: Shows `α` satisfies `IsDualOf E α (isogDual E α)` symmetrically — uses `degree_isogDual` to equate `deg(α̂)` with `deg(α)`, then applies `self_comp_isogDual` and `isogDual_comp_self`; concludes by `isogDual_unique`.
- **Hypotheses**: `0 < α.degree`; depends on `exists_dual` sorry.
- **Uses from project**: `isogDual`, `isogDual_unique`, `degree_isogDual`, `self_comp_isogDual`, `isogDual_comp_self`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 229–236, proof length ~8 lines
- **Notes**: Carries `sorry` via `exists_dual`.

---

### `theorem isogDual_add_of_sum_dual`

- **Type**: `(α β αβ : Isogeny E E) (h_sum_dual : (isogDual E αβ).toAddMonoidHom = (isogDual E α).toAddMonoidHom + (isogDual E β).toAddMonoidHom) : ∃ γ : Isogeny E E, γ.toAddMonoidHom = ... ∧ γ = isogDual E αβ`
- **What**: Silverman III.6.2(c) parametric form: given that `(α+β)̂ = α̂ + β̂` as AddMonoidHoms (as hypothesis), packages the conclusion into an existential. The real content is the hypothesis.
- **How**: Trivial term proof `⟨isogDual E αβ, h_sum_dual, rfl⟩`.
- **Hypotheses**: Pointwise dual additivity `h_sum_dual` (the true mathematical content); depends on `exists_dual` via `isogDual`.
- **Uses from project**: `isogDual`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 254–263, proof length 1 line
- **Notes**: The real content III.6.2(c) is in the hypothesis; this is packaging only. Carries `sorry` via `isogDual`.

---

### `theorem dual_add_of_trace_witnesses`

- **Type**: `(α β αβ α_dual β_dual αβ_dual : Isogeny E E) (tα tβ tαβ : ℤ) (hαβ_hom ...) (hα_trace ...) (hβ_trace ...) (hαβ_trace ...) (h_tr_add : tαβ = tα + tβ) : αβ_dual.toAddMonoidHom = α_dual.toAddMonoidHom + β_dual.toAddMonoidHom`
- **What**: Silverman III.6.2(c) witness-parametric: given integer trace witnesses for `α`, `β`, `α+β` at the AddMonoidHom level and trace additivity `tαβ = tα + tβ`, concludes dual additivity without mentioning `isogDual`.
- **How**: Evaluates all hypotheses pointwise at `P` via `congr_fun (congr_arg DFunLike.coe ...)`, solves for each dual term using `abel`, then combines via `add_zsmul` and trace additivity.
- **Hypotheses**: Trace identities at AddMonoidHom level for all three isogenies and their duals; additivity of traces. Does NOT depend on `exists_dual`.
- **Uses from project**: `mulByInt` (via `mulByInt_apply` `rfl` rewrite).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 280–311, proof length ~32 lines
- **Notes**: Proof > 30 lines. `exists_dual`-free (witness-parametric). Core mathematical content of III.6.2(c).

---

### `theorem dual_add_of_sum_witnesses`

- **Type**: `(α β αβ α_dual β_dual αβ_dual : Isogeny E E) (hαβ_hom ...) (h_sum : α.toAddMonoidHom + α_dual.toAddMonoidHom + (β.toAddMonoidHom + β_dual.toAddMonoidHom) = αβ.toAddMonoidHom + αβ_dual.toAddMonoidHom) : αβ_dual.toAddMonoidHom = α_dual.toAddMonoidHom + β_dual.toAddMonoidHom`
- **What**: Minimal witness form of III.6.2(c): given a single bundled sum identity at the AddMonoidHom level, concludes dual additivity. Simpler than `dual_add_of_trace_witnesses`.
- **How**: Rewrites `αβ` using `hαβ_hom`, evaluates pointwise, uses `abel` to rearrange, concludes by `add_left_cancel`.
- **Hypotheses**: `hαβ_hom`: `αβ` is the sum `α + β` as AddMonoidHoms; `h_sum`: combined trace-sum identity. `exists_dual`-free.
- **Uses from project**: none explicitly.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 319–336, proof length ~18 lines
- **Notes**: `exists_dual`-free alternative to `dual_add_of_trace_witnesses`.

---

### `theorem isogDual_mulByInt_of_comp`

- **Type**: `(n : ℤ) (hn : n ≠ 0) (h_comp : (mulByInt E n).comp (mulByInt E n) = mulByInt E ((mulByInt E n).degree : ℤ)) : isogDual E (mulByInt E n) = mulByInt E n`
- **What**: Silverman III.6.2(b) scalar case: `[n]̂ = [n]` (the dual of multiplication-by-n is itself), given the hypothesis that `[n] ∘ [n] = [deg [n]]` (which encodes `n² = n²`).
- **How**: Shows `mulByInt E n` satisfies `IsDualOf E (mulByInt E n) (mulByInt E n)` via `⟨h_comp, h_comp⟩`, then applies `isogDual_unique`.
- **Hypotheses**: `n ≠ 0`; hypothesis `h_comp` (consequence of T-III-4-020, not yet formalized); depends on `exists_dual` sorry via `isogDual_unique`.
- **Uses from project**: `mulByInt`, `isogDual_unique`, `IsDualOf`, `isogDual`.
- **Used by**: unused in file (called by `MulByIntDual.lean`).
- **Visibility**: public
- **Lines**: 344–350, proof length ~6 lines
- **Notes**: The hypothesis `h_comp` is noted as a consequence of `mulByInt_comp_eq_mul` (T-III-4-020, not yet formalized). Carries `sorry` via `isogDual_unique`.

---

### `theorem isogTrace_eq_dual`

- **Type**: `(α : Isogeny E E) (one_sub_α : Isogeny E E) (h_sum : α.toAddMonoidHom + (isogDual E α).toAddMonoidHom = (mulByInt E (isogTrace α one_sub_α)).toAddMonoidHom) : ∀ P : E.Point, α.toAddMonoidHom P + (isogDual E α).toAddMonoidHom P = (isogTrace α one_sub_α : ℤ) • P`
- **What**: Silverman III.8 parametric form: given `α + α̂ = [tr α]` as an AddMonoidHom identity, evaluates it pointwise to get `α(P) + α̂(P) = tr(α) • P`.
- **How**: Evaluates `h_sum` pointwise via `congr_fun (congr_arg DFunLike.coe ...)`, then rewrites using `mulByInt_apply`.
- **Hypotheses**: Pointwise hypothesis `h_sum` (the real content, from III.8.6 via dual additivity); depends on `exists_dual` via `isogDual`.
- **Uses from project**: `isogDual`, `isogTrace` (Endomorphism.lean), `mulByInt`, `mulByInt_apply` (Basic.lean).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 375–384, proof length ~9 lines
- **Notes**: Carries `sorry` via `isogDual`.

---

### `theorem isogDual_comp_self_apply`

- **Type**: `(α : Isogeny E E) (P : E.Point) : (isogDual E α).toAddMonoidHom (α.toAddMonoidHom P) = (α.degree : ℤ) • P`
- **What**: Pointwise version of `isogDual_comp_self`: `α̂(α(P)) = deg(α) • P` for every point `P`.
- **How**: Applies `congr_fun (congr_arg DFunLike.coe (congr_arg Isogeny.toAddMonoidHom (isogDual_comp_self E α))) P`.
- **Hypotheses**: Depends on `exists_dual` sorry via `isogDual_comp_self`.
- **Uses from project**: `isogDual_comp_self`, `isogDual`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 396–399, proof length ~4 lines
- **Notes**: Carries `sorry` via `isogDual_comp_self`.

---

## Summary Table

| Declaration | Kind | Lines | Sorry |
|---|---|---|---|
| `IsDualOf` | def | 49–50 | no |
| `exists_dual_of_construction` | theorem | 82–88 | no |
| `exists_dual_of_constructor` | theorem | 94–100 | no |
| `exists_dual_iff_constructor` | theorem | 106–114 | no |
| `exists_dual` | theorem | 141–142 | **yes** |
| `isogDual_comp_self_of_witness` | theorem | 154–157 | no |
| `self_comp_isogDual_of_witness` | theorem | 159–162 | no |
| `degree_dual_of_witness` | theorem | 167–179 | no |
| `isogDual` | noncomputable def | 185–186 | transitive |
| `isogDual_spec` | theorem | 189–190 | transitive |
| `isogDual_comp_self` | theorem | 193–195 | transitive |
| `self_comp_isogDual` | theorem | 198–200 | transitive |
| `isogDual_unique` | theorem | 204–206 | transitive |
| `degree_isogDual` | theorem | 212–222 | transitive |
| `isogDual_isogDual` | theorem | 229–236 | transitive |
| `isogDual_add_of_sum_dual` | theorem | 254–263 | transitive |
| `dual_add_of_trace_witnesses` | theorem | 280–311 | no |
| `dual_add_of_sum_witnesses` | theorem | 319–336 | no |
| `isogDual_mulByInt_of_comp` | theorem | 344–350 | transitive |
| `isogTrace_eq_dual` | theorem | 375–384 | transitive |
| `isogDual_comp_self_apply` | theorem | 396–399 | transitive |

---

## Key API (used by 3+ others in this file)

- `IsDualOf`: used by all `exists_dual_*`, `isogDual_*_of_witness`, `isogDual_spec`, `isogDual_unique`, `isogDual_isogDual`, `isogDual_mulByInt_of_comp` (10+ uses).
- `exists_dual`: used by `isogDual`, `isogDual_spec`, `isogDual_unique` (3 uses in proof bodies).
- `isogDual`: used by `isogDual_spec`, `isogDual_comp_self`, `self_comp_isogDual`, `isogDual_unique`, `degree_isogDual`, `isogDual_isogDual`, `isogDual_add_of_sum_dual`, `isogTrace_eq_dual`, `isogDual_comp_self_apply`, `isogDual_mulByInt_of_comp` (10+ uses).
- `isogDual_comp_self`: used by `degree_isogDual`, `isogDual_isogDual`, `isogDual_comp_self_apply` (3 uses).
- `isogDual_unique`: used by `isogDual_isogDual`, `isogDual_mulByInt_of_comp` (2 uses), referenced in docstring of `degree_isogDual`.
- `isogDual_spec`: used by `isogDual_comp_self`, `self_comp_isogDual` (2 uses).

---

## Unused in file

- `exists_dual_iff_constructor`
- `isogDual_comp_self_of_witness`
- `self_comp_isogDual_of_witness`
- `degree_dual_of_witness`
- `isogDual_isogDual`
- `isogDual_add_of_sum_dual`
- `dual_add_of_trace_witnesses`
- `dual_add_of_sum_witnesses`
- `isogDual_mulByInt_of_comp`
- `isogTrace_eq_dual`
- `isogDual_comp_self_apply`
