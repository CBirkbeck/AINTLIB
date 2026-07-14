# Decomposition — BB-QF `mulByHom_locallyQuasiFinite` (Torsion:141) — STREAM-G0 v10.219

**Scoped by G0, 2026-07-14.** Target: `LocallyQuasiFinite (E.mulByHom N)` for `N ≠ 0`, ANY base `S`,
ANY characteristic (incl. `p ∣ N`). KM 2.3.1's fibre route, executed against mathlib's
`locallyQuasiFinite_iff_finite_preimage_singleton` (QuasiFinite.lean:318: `[LocallyOfFiniteType f]
[QuasiCompact f]` ⟹ `LocallyQuasiFinite f ↔ ∀ x, (f ⁻¹' {x}).Finite`).

## Route survey (why THIS decomposition)
- Unramified route (`mulByHom_formallyUnramified'`): sorry-backed in-tree (BB-DIFF L-BC,
  MulByHomUnramified:158) AND only covers `N` invertible. NOT a discharge.
- `mulByHom_surjective` (MulByHomDegree): CIRCULAR — assumes `[Flat][IsFinite]` of `[N]` (the boxes).
- finrank/`le_finrank_of_killed_injective`/EtaleSectionsCount: all box-conditional. NOT usable.
- Division-polynomial torsion bridge: NOT in mathlib (only Ψ/degree data); building it = KM's K4
  carve-out. AVOIDED.
- **CHOSEN**: topological fibre argument on the fibre curve + HasseWeil's sorry-free field-level
  torsion cardinalities (cross-project import — the AINTLIB point) for the nonconstancy witness.

## Leaf tree

| Leaf | Content | Status/route |
|---|---|---|
| [QF-L1] | `LocallyOfFiniteType (mulByHom N)` + `QuasiCompact (mulByHom N)` | from `mulByHom_isProper` (IsProper extends lft+separated+UC; UC ⟹ qc or via cancellation against π) |
| [QF-L2] | fibre-set reduction: `((mulByHom N) ⁻¹' {y}).Finite` ⟸ same on the fibre curve `E_{κ(s)}`, `s := π y` | preimage ⊆ π⁻¹(s) (mulByHom_π); compare via mathlib fibre machinery (`Scheme.Hom.fiber`?) + `mulByHom_baseChange` (T-D6a-ii, HAVE) |
| [QF-L3] | MODEL BRIDGE over a field: `E'/Spec k ≅ modelEllipticCurve W` (or the homeo of total spaces intertwining `[N]` and model-`[N]`) | from `localModel` (LocallyWeierstrass over Spec k: any nonempty affine open of Spec k is ⊤); CHECK in-tree first (Comparison/ModelRecord/K4 layers) |
| [QF-L4] | CURVELIKE: on `projModel W` over a field, every non-generic point is closed (⟹ proper irreducible closed subsets are singletons; + Noetherian ⟹ proper closed subsets finite) | chains through a point live in an affine chart (opens are generization-stable); chart ring ≅ `W.CoordinateRing`-family (K4's `zChartSectionCoordRingEquiv` precedent); `ringKrullDim ≤ 1` via k[x,y]/(f): PIT/`ringKrullDim` mathlib-hunt |
| [QF-L5] | WITNESS: `mulByHom N ≠ π ≫ zero` — via ∃ `P : W_{k̄}.Point`, `N • P ≠ 0` | HasseWeil sorry-free: `torsion_ellPow_finite`/`card_torsion_ellPow_nat` (#E[ℓⁿ] = ℓ²ⁿ, ℓ ≠ char) ⟹ `p^a •`-image infinite (injective on E[ℓⁿ], gcd = 1) ⊄ E[m] finite ⟹ ∃ P with N•P ≠ 0. Transport: `projModelPointsEquiv_zsmul` (MulByHomDegree, HAVE) + model base-change compat |
| [QF-L6] | field-level core: `∀ y', (([N] on E'_κ) ⁻¹' {y'}).Finite` | assembly: [N]⁻¹(cl y) closed (proper [N] ⟹ closed map); infinite ⟹ some irreducible component = whole curve (L4 + Noetherian) ⟹ y closed ⟹ [N] ≡ const = zero-pt ⟹ E[N]-subscheme = E (integrality) ⟹ `[N] = π ≫ zero` ⟹ ✗L5. Generic-y case: [N]⁻¹{η} ⊆ {η} via closed-map + L4 |
| [QF-L7] | assembly: L1 + (∀ y, L2∘L6) → `locallyQuasiFinite_iff_finite_preimage_singleton` | mechanical |

Char-p safety: NO separability, NO division polynomials, NO E[p]-structure anywhere — the witness
uses only prime-to-char torsion; the topology handles [p] uniformly.

## Consumers on discharge
`mulByHom_isFinite` (Torsion:156) closes outright (proper + lqf, ZMT) ⟹ `torsionπ_isFinite` real ⟹
the SIGNAL/Y₀(N) `quotientHom_finite`-adjacent box trail and E[N]-package finiteness auto-clean
(BB-QF eliminated from the register).
