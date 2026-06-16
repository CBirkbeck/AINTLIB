# Integration of reviewer reply — 2026-05-11 T205-d residual closure brief

**Reply received:** 2026-05-11 (frontier LLM reviewer, DS conventions)
**Reply file:** `reply.md` (verbatim transcript)
**Brief file:** `brief.md`
**State file:** `state.md`

## Summary of reviewer guidance

The reviewer **confirms Q1 (soundness)** of the restructured consumer chain:
the symmetric form `petN(T_p f, g) = petN(⟨u⟩f, T_p g)` does imply the
unsymmetric DS standard form `petN(T_p f, g) = petN(f, ⟨u⟩⁻¹ T_p g)` via
diamond unitarity, and then Hecke/diamond commutation gives the canonical
form. So the consumer chain from `_from_petN_symmetric_form` is valid.

The reviewer **rules against all four originally proposed paths** as primitive
worker targets and **prescribes a four-step alternative chain**:

| Reviewer's verdict | Path |
|---|---|
| ❌ wrong primitive target | A (direct DS 5.5.2(b) monolithic σ_p reindex) |
| ❌ not a shortcut | B (Atkin–Lehner–Li orthogonality — same adjoint infrastructure) |
| ❌ wrong problem | C (U_p decomposition — bad-prime theory) |
| ❌ not actionable | D (mathlib wait) |
| ✅ correct chain | **Path A revised**: ADJ-WRAPPER → ADJ-CORR → DIAMOND-SPEC → UNSYMM → SYMM |

### The critical reframe

> "Do not make the worker prove a direct equality of the two unfolded sums
> in §7 as a monolithic σ_p-reindex. Prove the adjugate correspondence
> theorem first, then handle the T_p-specific diamond identification
> separately."

### The β ↔ β' trap (reviewer's most important warning)

> "For Hecke adjoints, adjugates of **left** coset representatives naturally
> become **right** coset representatives. A clean left-representative map
> β_b ↦ β_{b'} should not be expected in that naive form."

Worked example at level 1:
```
β_b* = diag(p, -b; 0, 1) = shift(-b) · diag(p, 0; 0, 1)
```
All these adjugates lie in the **same left coset**, although they are
distinct as transposed correspondence data. This is why per-β balancing
fails. The bijection lives on the **finite correspondence / tile index /
right-left quotient data**, not on the displayed upper-triangular reps.

### The natural theorem

> "Sum over all representatives — only then does the collection of domains
> tile the correct finite-index subgroup quotient. **This is the actual
> content of DS 5.5.3.**"

The reviewer recommends targeting
```
∑_{β ∈ R(Γ\ΓαΓ)} ⟨f|_k β, g⟩_Γ = ∑_{β' ∈ R(Γ\Γα*Γ)} ⟨f, g|_k β'⟩_Γ
```
where the right side is **not** the naive pointwise β ↦ β* map but the
**transposed finite correspondence**. The FD-transport theorem already
formalized (T205-d-API-1, ✅) is exactly the right analytic foundation.

For α = diag(1,p), α* = diag(p,1). The adjugate double coset is identified
with the original T_p double coset after the diamond correction ⟨u⟩⁻¹.
**This is where σ_p, the Γ₀/Γ₁ quotient action, and the triple-product
identities belong — they should NOT be mixed into the analytic
correspondence-adjoint theorem.**

## Mapping of questions → reviewer answers

| # | Question | Reviewer answer (one-line) |
|---|---|---|
| Q1 | Soundness of symmetric ⇒ unsymmetric chain | ✅ YES — diamond unitarity + Hecke/diamond commutation |
| Q2 | Path selection (A/B/C/D + LOC) | Revise Path A organization (4-step chain); B not a shortcut; C wrong problem; D inactionable. **350–650 LOC total.** |
| Q3 | Sub-lemma decomposition (A1-A5) | Replace with: ADJ-WRAPPER (30-100) + ADJ-CORR (150-300, real work) + DIAMOND-SPEC (150-250) + UNSYMM (30-50) + SYMM (30-50) |
| Q4 | Alternative formulations | Adjugate double-coset correspondence is the natural primitive target — not the symmetric form itself |
| Q5 | σ_p Q-permutation on Hecke reps β ↔ β' | **TRAP** — naive β_b ↦ β_b' on displayed upper-triangular reps does not exist (collapse in same left coset). Bijection lives on transposed correspondence data. |
| Q6 | Path B circularity | Uses same analytic adjoint infrastructure; not a shortcut. Park Path B. |
| Q7 | Strategic priority (T205-d vs L-fns vs mathlib wait) | Do T205-d-SYMM chain. Do not pursue Paths B or C as workarounds. |

## Ticket-board changes applied

### Superseded (kept in tickets.md with SUPERSEDED markers)

- `T205-d-API-2-DC-IUNION-M` — bundled σ_p with analytic correspondence
- `T205-d-API-2-DC-IUNION-T` — same as above
- `T205-d-API-2-DC-CLOSE` — bundled too much; via_iUnion_residuals consumer too coarse
- `T205-d-SYMM-DIRECT` (informal label, was in closure paths block) — direct monolithic σ_p reindex rejected by reviewer as wrong primitive

### New tickets added (per reviewer's four-step chain)

| Ticket | Step | Statement | LOC | Depends on |
|---|---|---|---|---|
| `T205-d-ADJ-WRAPPER` | 1 | `peterssonInner_slash_adjoint_for_heckeRep` — wrapper around existing `peterssonInner_slash_adjoint` for a Hecke representative β | 30–100 | `peterssonInner_slash_adjoint` (✅) |
| `T205-d-ADJ-CORR` | 2 | `petN_doubleCoset_adjoint_adjugate` — finite-correspondence aggregation theorem (the real analytic work) | 150–300 | T205-d-API-1 (✅), T205-d-ADJ-WRAPPER |
| `T205-d-DIAMOND-SPEC` | 3 | `heckeT_p_adjugate_correspondence_eq_diamond_inv_T_p` — T_p-specific identification of adjugate aggregate with `⟨u⟩⁻¹ T_p` | 150–250 | T205-d-ADJ-CORR + existing diamond infra |
| `T205-d-UNSYMM` | 4a | `petN_heckeT_p_adjoint_standard_form` (DS 5.5.3 unsymmetric form) | 30–50 | T205-d-ADJ-CORR, T205-d-DIAMOND-SPEC |
| `T205-d-SYMM` | 4b | `petN_heckeT_p_symmetric_form` — closure via diamond unitarity (the existing sorry at line ~17422) | 30–50 | T205-d-UNSYMM, diamond unitarity (T100a ✅) |

**Acceptance for next worker pass** (reviewer's "next report" criterion):
either a compiling `T205-d-ADJ-CORR` theorem for Γ₁(N), α = diag(1,p),
or one exact missing FD/integrability/transversal lemma blocking it.

### Closure-paths section (top of tickets.md) replaced

Old `T205-d restructuring landed 2026-05-11 (beastmode)` "Closure
strategies" enumeration replaced with `T205-d-SYMM closure chain —
restructured per expert review 2026-05-11`, listing the new 5-ticket
chain plus the critical β ↔ β' trap warning.

## Task list updates

Superseded tasks deleted from task list:
- #13 (T205-d-API-2-DC-IUNION-M)
- #14 (T205-d-API-2-DC-IUNION-T)
- #15 (T205-d-API-2-DC-CLOSE)
- #16 (T205-d-SYMM-DIRECT)

New tasks added with dependency chain ADJ-WRAPPER → ADJ-CORR → DIAMOND-SPEC
and (ADJ-CORR ∧ DIAMOND-SPEC) → UNSYMM → SYMM:
- #17 T205-d-ADJ-WRAPPER
- #18 T205-d-ADJ-CORR (blocked by #17)
- #19 T205-d-DIAMOND-SPEC (blocked by #18)
- #20 T205-d-UNSYMM (blocked by #18, #19)
- #21 T205-d-SYMM (blocked by #20)

## Defensive code-review checklist for the worker (from reviewer)

When implementing T205-d-ADJ-CORR and T205-d-DIAMOND-SPEC:

1. ❗ **The β ↔ β' trap.** Adjugates of a left transversal collapse as
   left cosets. Do NOT model the correspondence as a function on the
   displayed upper-triangular reps. Use transposed correspondence /
   right-left quotient data.

2. ❗ **No circularity.** Any derivation of the symmetric form from
   the unsymmetric form is circular UNLESS the unsymmetric form was
   independently proved via the adjugate correspondence. Safe route:
   ```
   single-slash adjoint + FD transport
     → double-coset adjugate theorem (ADJ-CORR)
     → T_p-diamond specialisation (DIAMOND-SPEC)
     → unsymmetric/canonical form (UNSYMM)
     → symmetric form (SYMM)
   ```

3. ❗ **Don't overgeneralize.** Minimal non-circular theorem is for
   Γ = Γ₁(N), α = diag(1,p), p ∤ N. Generalise only after closure.

4. ❗ **Separate AE-disjointness/integrability/null-measurability
   wrappers** around T205-d-API-1 — do NOT fold them into ADJ-CORR.

5. ❗ **Diamond/σ_p stays in DIAMOND-SPEC.** ADJ-CORR is the pure
   analytic correspondence-adjoint theorem; σ_p Q-permutation,
   triple-product identities, Γ₀/Γ₁ quotient action all live one
   layer up.

## Sources cited by reviewer

- DS §5.5 (Theorem 5.5.3, Proposition 5.5.2(b))
- DS §5.5.3 (sum-over-representatives FD tiling — "the actual content
  of DS 5.5.3")
- Miyake §4.5 (Theorems 4.5.4, 4.5.5) — referenced but not cited as
  primary source for the chain

## Open questions for next reviewer round (if needed)

The reviewer's brief is self-contained and the chain is clear. Any
follow-up reviewer round should be **after** ADJ-CORR is in flight,
and would focus on:
- whether the transposed-correspondence data formalisation in Lean
  matches what the reviewer envisaged
- whether the DIAMOND-SPEC right-transversal-then-convert technique
  succeeds as expected at the Γ₁(N) level
- whether the AE-disjointness wrappers around T205-d-API-1 are
  cheap or expensive in practice
