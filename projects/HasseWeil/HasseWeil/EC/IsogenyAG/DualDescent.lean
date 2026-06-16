import HasseWeil.EC.IsogenyAG.IsogenyClass

/-!
# DUAL-DESCENT — the dual isogeny over the base field (symmetry of isogeny)

Goal (see `.mathlib-quality/plan-dual-descent.md` + `tickets-dual-descent.md`): discharge
`UniversalDualWitness F` for a char-0 base field `F` (esp. `ℚ`) — every isogeny over `F` has an
`F`-rational dual, i.e. `IsIsogenous` is symmetric, i.e. the `IsogenyClass` quotient and the LMFDB
label layer become unconditional.

**Route (Silverman III.6.1, transcribed):** over char 0 every isogeny is separable, so the dual is
purely the III.4.11 factorization `ker φ ⊆ E[m] ⟹ [m] = φ̂ ∘ φ`. III.4.11 is irreducibly a
`K̄`-Galois argument, so the dual is built over `K̄ = AlgebraicClosure F` (existing K̄ machinery) and
**descended to `F` by uniqueness + Galois-invariance** (`φ̂^σ ∘ φ = [m] ⟹ φ̂^σ = φ̂`). The descent is
run at a *finite* Galois level `L/F`. The new infrastructure is the descent of a curve morphism
(DUAL-Q2, the deep crux); this file holds the headline + assembly, with the descent internals filled
in across tickets DUAL-Q1…Q4.

This is a scaffold: the headline below is `sorry` (it elaborates against the existing
`UniversalDualWitness`); the Galois-action / descent internals land per the ticket board.
-/

namespace HasseWeil.EC

open WeierstrassCurve

/-- **DUAL-Q4 headline** (Silverman III.6.1, char-0 case): every isogeny over a char-0 field has an
`F`-rational dual — i.e. `UniversalDualWitness F` holds. Proof route: base-change each isogeny to
`AlgebraicClosure F`, take the dual there (existing K̄ machinery; char 0 ⟹ separable), and descend
to `F` by Galois-invariance + uniqueness (DUAL-Q1–Q3). Scaffold: filled across the DUAL-DESCENT
tickets. -/
theorem universalDualWitness_of_charZero (F : Type*) [Field F] [DecidableEq F] [CharZero F] :
    UniversalDualWitness F := by
  sorry

/-- Symmetry of `IsIsogenous` over a char-0 field — the LMFDB-label gate, discharged from the
headline. -/
theorem isIsogenous_symm_charZero {F : Type*} [Field F] [DecidableEq F] [CharZero F]
    {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic] (h : IsIsogenous W₁ W₂) :
    IsIsogenous W₂ W₁ :=
  h.symm_of (universalDualWitness_of_charZero F)

end HasseWeil.EC
