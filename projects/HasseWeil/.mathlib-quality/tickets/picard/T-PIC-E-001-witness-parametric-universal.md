# T-PIC-E-001: Witness-parametric universal `AddHomProperty`

**Status**: OPEN
**Silverman**: III.4.8 — the universal hom property
**Module**: `HasseWeil/EC/IsogenyAG/HomProperty.lean`
**Owner**: —
**Estimated lines**: ~40
**Difficulty**: easy (after dependencies)
**Phase**: E

## Depends on
- T-PIC-A-004 (`picZeroSumHom`)
- T-PIC-B-001 (`picZeroOfPoint`)
- T-PIC-B-003 (`picZeroSum_picZeroOfPoint = id`)
- T-PIC-C-004 (`pushforwardPicZero` group hom)
- T-PIC-D-001 (diagram commute)

## Blocks
- T-PIC-F-003 (final B-4-003 closure)

## Statement

The universal `AddHomProperty` parametrized by σ̄-iso witnesses:

```lean
/-- **Silverman III.4.8 (witness-parametric form)**: every isogeny is a
group homomorphism on points, given σ̄-iso witnesses on both source and
target. The witnesses provide the bijection direction `κ ∘ σ̄ = id`,
which combined with `σ̄ ∘ κ = id` (T-PIC-B-003) makes σ̄ injective. -/
theorem AddHomProperty_of_picZero_iso
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (h₁ : ∀ D : PicProj₀ (⟨W₁⟩ : Curves.SmoothPlaneCurve F),
            picZeroOfPoint W₁ (picZeroSum W₁ D) = D)
    (h₂ : ∀ D : PicProj₀ (⟨W₂⟩ : Curves.SmoothPlaneCurve F),
            picZeroOfPoint W₂ (picZeroSum W₂ D) = D) :
    φ.AddHomProperty cd
```

`h_i` is the "κ ∘ σ̄ = id" direction, which is what T-PIC-F-001 will
provide unconditionally once T-III-3-003 lands. Until then, this
witness-parametric form decouples our work from worker-K's progress.

## Mathlib check
N/A (project-internal).

## Naming
`AddHomProperty_of_picZero_iso`.

## Generality
Same as Phase C/D defaults.

## Proof approach

```lean
theorem AddHomProperty_of_picZero_iso ... := by
  intro P Q
  -- Goal: φ.toPointMap cd (P + Q) = φ.toPointMap cd P + φ.toPointMap cd Q
  -- Strategy: pull both sides through κ, where they agree.

  -- Apply h₂ to both sides (using picZeroOfPoint as left inverse of picZeroSum):
  apply (Function.LeftInverse.injective (g := picZeroSum W₂) ?_)
  · -- After this, goal: κ(LHS) = κ(RHS)
    rw [picZeroOfPoint_pushforwardPicZero]   -- LHS = φ_∗(κ P+Q)
    rw [picZeroOfPoint_pushforwardPicZero,
        picZeroOfPoint_pushforwardPicZero]   -- RHS = φ_∗(κ P) + φ_∗(κ Q)
    -- Now κ is a group hom (need this — extracted as lemma):
    rw [picZeroOfPoint_add]                  -- κ(P+Q) = κ P + κ Q
    -- Apply group hom property of pushforwardPicZero:
    rw [map_add]
  · -- Provide the LeftInverse witness:
    intro D; exact h₂ D
```

The proof needs:
- `picZeroOfPoint_add : κ(P+Q) = κ(P) + κ(Q)`. This is implicit in Pic⁰
  being a group structure but needs to be checked. May need its own
  lemma.

Wait — `picZeroOfPoint` is `P ↦ class((P) - (O))`. The fact that
`picZeroOfPoint(P + Q) = picZeroOfPoint(P) + picZeroOfPoint(Q)` is
**equivalent** to `(P+Q) - (O) ~ (P) - (O) + (Q) - (O)`, which says
`(P+Q) + (O) ~ (P) + (Q)`, the **defining relation of the group law on E
via Pic⁰**. This is a **non-trivial** identity — but it's exactly what
Silverman III.3.4(e) proves geometrically using divisors of lines.

So the proof of T-PIC-E-001 has TWO steps:
1. Establish `picZeroOfPoint_add` (T-PIC-A-002 already proves this for
   principal-divisor side, but we need it explicitly as a separate fact).
2. Combine with the diagram commute and σ̄ injectivity to conclude.

**Actually**, on reflection, `picZeroOfPoint_add` ≡ Silverman III.3.4(e),
which IS a substantial theorem. We may need to add a sub-ticket
T-PIC-E-001a for this. **Mark as todo for ticket-writing review.**

## Acceptance criteria

`#print axioms HasseWeil.EC.Isogeny.AddHomProperty_of_picZero_iso` reports
only standard axioms.

## Open question

Does `picZeroOfPoint_add` follow naturally from our existing setup, or
does it require its own substantial proof (Silverman III.3.4(e),
divisors of three collinear lines)?

If it requires its own proof: add T-PIC-E-001a (~80 lines, depends on
T-PIC-A-002).

## Progress log
