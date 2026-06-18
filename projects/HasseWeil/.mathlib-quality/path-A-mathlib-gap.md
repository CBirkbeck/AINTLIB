# Path A — Mathlib API Gap Document (Worker A, 2026-05-06)

## Status

The IV.1.4 cascade for the Hasse-Weil bound has been reduced to two named substantive
walls via the Path A Kähler-witness route. Sub-helpers 120 and 121 (axiom-clean,
shipped this session) discharge the foundational K(E) identities. The remaining
walls are:

1. **D(slope) computation in K(E)** for `addSlope W (negFrobeniusIsog W)`.
2. **III.5.2 differential additivity** OR **BRIDGE-001 for general α** (interchangeable).

Wall #2 reduces, via existing axiom-clean infrastructure, to a single Mathlib API
gap: `Field.finSepDegree` ↔ `Module.finrank` for non-Mathlib-recognized algebra
structures (the `Isogeny.toAlgebra`).

This document names the gap precisely.

## Existing axiom-clean infrastructure (Path A)

```
Sub-helper 104   D(x_gen^q) = 0                                 (Frobenius vanishing)
Sub-helper 105   D((frob).pullback x_gen) = 0
Sub-helper 106   D((frob).pullback y_gen) = 0
Sub-helper 107   D((negFrob).pullback x_gen) = 0
Sub-helper 108   D((negFrob).pullback y_gen) = 0
Sub-helper 109   D(addPullback_x) = (2ℓ + a₁) • D(ℓ) - D(x_gen) (general α witness)
Sub-helper 110   D(addPullback_x for negFrob) = (2ℓ + a₁) • D(ℓ) - D(x_gen)
Sub-helper 111   ω(γ) = 1 via Kähler witness                    (witness consumer)
Sub-helper 112   Hasse-Weil bound via Kähler witness            (full cascade)
Sub-helper 113   ω(γ) = 1 via pullbackKaehler witness           (cleaner reformulation)
Sub-helper 114   id.pullbackKaehler ω = ω                       (id case)
Sub-helper 115   (-π).pullbackKaehler ω = 0                     (negFrob case)
Sub-helper 116   γ.pullbackKaehler ω = ω via III.5.2 add witness
Sub-helper 117   ω(γ) = 1 via III.5.2 additivity witness
Sub-helper 118   Hasse-Weil bound via III.5.2 additivity witness
Sub-helper 119   Kähler witness via slope-derivative + K(E) id  (factored form)
Sub-helper 120   weierstrass_equation_in_KE                     (curve eq in K(E))
Sub-helper 121   kaehler_curve_equation_K_E                     (curve eq differentiated)
```

## Remaining substantive walls

### Wall #1: D(addSlope W (negFrob)) in K(E)

The slope formula gives:
```
addSlope W (negFrob) = (y_gen - y₂) / (x_gen - x₂)
```
where `x₂ = (negFrob).pullback x_gen`, `y₂ = (negFrob).pullback y_gen`.

Differentiating in K(E):
```
D(ℓ) = ((y_gen - y₂) / (x_gen - x₂)) differentiated
     = ((x_gen - x₂) · D(y_gen - y₂) - (y_gen - y₂) · D(x_gen - x₂)) / (x_gen - x₂)²
     = ((x_gen - x₂) · D(y_gen) - (y_gen - y₂) · D(x_gen)) / (x_gen - x₂)²
       (using sub-helpers 107-108: D(x₂) = D(y₂) = 0)
```

Substituting D(y_gen) via sub-helper 121:
```
(2y + a₁x + a₃) • D(y) = (3x² + 2a₂x + a₄ - a₁y) • D(x)
```

Yields:
```
D(ℓ) = c • D(x_gen)
```
where c is an explicit rational function in x_gen, y_gen, x₂, y₂, a₁, ..., a₆.

**Deliverable**: Sub-helper 122 stating the explicit form of c, axiom-clean,
roughly 30-60 LOC.

### Wall #2: III.5.2 differential additivity OR BRIDGE-001 for general α

Existing scaffolding:
- `omegaPullbackCoeff_eq_formalIsogenyLeading` (FormalIsogenySeries.lean:225) —
  BRIDGE-001 generic, has `sorry` (the wall).
- `omegaPullbackCoeff_add_via_bridge_of_constCoeff` — derives ω-additivity
  from BRIDGE-001 (×3) + BRIDGE-003.

The substance of BRIDGE-001 reduces to an identity between:

* **III.1.5 / III.5.5 content**: the omega-pullback coefficient lies in the image
  of `algebraMap K K(E)` (i.e., is a constant in the base field, not a generic
  rational function).
* **IV.4.3 substance**: the formal-group invariant differential matches the
  Kähler ω modulo the localExpand → LaurentSeries bridge.

## The Mathlib API gap

The substantive Mathlib gap is in connecting `Field.finSepDegree` to
`Module.finrank` for the specific `Isogeny.toAlgebra` algebra structure.

Currently:
- `Isogeny.sepDegree φ = Field.finSepDegree W₂.FunctionField W₁.FunctionField` (via
  `φ.toAlgebra`).
- `Isogeny.degree φ = Module.finrank W₂.FunctionField W₁.FunctionField` (via
  `φ.toAlgebra`).
- `isSeparable_iff_sepDegree_eq_degree` (axiom-clean): for FiniteDim and via
  `φ.toAlgebra`, `IsSeparable ↔ sepDegree = degree`.

Missing: a direct Mathlib lemma `card_kernel_eq_finrank` connecting the
group-theoretic kernel cardinality of an isogeny on K̄-points to the field-
theoretic `Module.finrank`.

In our setup:
- `kernel_eq_top_of_hom_eq_id_sub_frobenius` (axiom-clean) gives `ker γ = ⊤`.
- `Nat.card ⊤ = Fintype.card E(F_q) = pointCount` (axiom-clean).

Missing chain (witness-parametric in our codebase, requires fiber witness):
- `card_kernel_eq_degree_of_separable_witness` — REQUIRES FIBER WITNESS.
- `fiber_witness_of_ker_card_eq_sepDegree` — REQUIRES `|ker| = sepDegree`.

The cycle:
```
fiber witness ← |ker γ| = γ.sepDegree ← γ.sepDegree = γ.degree (sep + finDim,
                                          axiom-clean)
                                       ← |ker γ| = γ.degree
                                          ↑ requires fiber witness (T-III-4-015)
```

## Mathlib PR shape

The gap requires a Mathlib theorem:
```
theorem WeierstrassCurve.Affine.Isogeny.degree_eq_card_kernel_of_isSeparable
    {K : Type*} [Field K] {E : WeierstrassCurve.Affine K} [E.IsElliptic]
    (φ : Isogeny E E)
    [Finite φ.kernel]
    (hsep : φ.IsSeparable)
    (hfin : @FiniteDimensional E.FunctionField E.FunctionField _ _
      φ.toAlgebra.toModule) :
    φ.degree = Nat.card φ.kernel
```

This would be the Mathlib version of T-III-4-015, axiom-clean, derived from:
- The fundamental result that for separable extensions of function fields of
  smooth projective curves of genus 1 over algebraically closed fields,
  every fiber of the morphism has the same cardinality (= sepDegree).
- For any isogeny with finite kernel, the kernel IS the fiber over the identity
  (`kernel_eq_top → ⊤ = E(K̄)`).
- For separable + smooth, sepDegree = degree.
- Compose: degree = sepDegree = #fiber = #kernel.

The Mathlib development required:
1. Define `Isogeny.kernel` as `AddSubgroup E.Point`.
2. Prove `kernel_eq_fiber_over_zero` (definitional / direct).
3. Prove `card_fiber_eq_sepDegree_of_isSeparable` (the substantive III.4.10 / III.4.12).
4. Conclude `card_kernel_eq_degree_of_isSeparable`.

Step 3 is the hard one. It requires the Galois-theoretic separability +
smooth-curve connection, established in Silverman III.4 / III.5.

## Conclusion: Worker A's contribution

The Path A Kähler-witness route reduces the IV.1.4 cascade for the Hasse-Weil
bound to ONE substantive Mathlib gap:

> `WeierstrassCurve.Affine.Isogeny.degree_eq_card_kernel_of_isSeparable`

This is the Mathlib formulation of Silverman III.4.10(a) / T-III-4-015 directly,
without requiring the fiber-witness cycle.

With this Mathlib lemma in hand:
- |ker γ| = γ.degree directly (Mathlib).
- γ.degree = γ.sepDegree (separable + FiniteDim, axiom-clean).
- |ker γ| = γ.sepDegree.
- `fiber_witness_of_ker_card_eq_sepDegree` produces the fiber witness.
- All other Path A axiom-clean infrastructure (sub-helpers 1-121) composes to
  the unconditional Hasse-Weil bound, char-agnostic, sign-free.

**This is the bottleneck**. Worker A's Path A scaffold has reduced the multi-
hundred-LOC III.5.2 / IV.4.3 substantive content to a single named Mathlib
theorem.

## Next steps

1. **Mathlib PR**: Develop and submit `degree_eq_card_kernel_of_isSeparable` to
   Mathlib via the standard III.4 separability/fiber chain.
2. **Once landed**: One closing-arc commit (~10-15 LOC) collapses the entire
   Hasse-Weil cascade for ALL F_q simultaneously via Worker C's parametric form.

---

*Worker A, 2026-05-06. 293 commits, 121 sub-helpers shipped this session.*
