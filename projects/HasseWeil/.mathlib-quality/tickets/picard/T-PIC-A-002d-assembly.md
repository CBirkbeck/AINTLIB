# T-PIC-A-002d: Final assembly of σ vanishing on principal divisors

**Status**: DONE-VIA-PARENT (T-PIC-A-002's
`projectiveDivisorSum_eq_zero_of_principal` shipped; explicit
chord/vertical specializations also shipped in Miller.lean.)
**Silverman**: III.3.5
**Module**: `HasseWeil/Curves/PicZero.lean`
**Owner**: —
**Estimated lines**: ~50
**Difficulty**: easy
**Phase**: A (final assembly)

## Depends on

- T-PIC-A-002a (general line case)
- T-PIC-A-002b (vertical-line case, DONE)
- T-PIC-A-002c (factorization)
- Existing multiplicativity helpers (DONE):
  - `projectiveDivisorSum_projectiveDivisorOf_one`
  - `projectiveDivisorSum_projectiveDivisorOf_mul`
  - `projectiveDivisorSum_projectiveDivisorOf_inv`

## Blocks

- T-PIC-A-003 (descent of σ̄ to Pic⁰) — already DONE witness-parametrically;
  this provides the **unconditional** witness.
- T-PIC-F-003 (B-4-003 closure)

## Statement

```lean
theorem projectiveDivisorSum_projectiveDivisorOf
    [IsAlgClosed F]
    {f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField} (hf : f ≠ 0) :
    projectiveDivisorSum W
      ((⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf f) = 0
```

Corollary form (matching the witness needed by
`AddHomProperty_of_picZero_witnesses`):

```lean
theorem projectiveDivisorSum_principal
    [IsAlgClosed F]
    {D : ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)}
    (hD : D ∈ projPrincipalSubgroup ⟨W⟩) :
    projectiveDivisorSum W D = 0
```

## Proof approach

Pure assembly:

```lean
theorem projectiveDivisorSum_projectiveDivisorOf hf := by
  -- Step 1: Use factorization (A-002c)
  obtain ⟨c, xs, gs, h_eq⟩ := functionField_multiplicative_decomp f hf
  -- Step 2: σ ∘ projectiveDivisorOf is multiplicative (already shipped)
  rw [h_eq]
  rw [projectiveDivisorSum_projectiveDivisorOf_mul, ...]
  -- Step 3: Each factor vanishes
  · simp [projectiveDivisorOf_const]   -- units
  · exact projectiveDivisorSum_vertical_line _ -- vertical lines (A-002b)
  · exact projectiveDivisorSum_lineForm_zero_of_collinear _ -- lines (A-002a)
```

## Acceptance criteria

```lean
#print axioms HasseWeil.Curves.projectiveDivisorSum_projectiveDivisorOf
#print axioms HasseWeil.Curves.projectiveDivisorSum_principal
```
both report only standard axioms.

## Risks

Low. All ingredients are statements; the assembly is straightforward
chaining. ~50 LOC.

## Progress log
