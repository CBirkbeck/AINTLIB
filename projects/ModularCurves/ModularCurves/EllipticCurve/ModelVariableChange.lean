import ModularCurves.EllipticCurve.PoleFiltration
import ModularCurves.ForMathlib.AffinePointVariableChange

/-!
# Variable changes on the projective Weierstrass model, and the comparison theorem

**(T-W7 skeleton, lanes P3/P5 — `/develop --decompose` 2026-07-07.)** The action of
`WeierstrassCurve.VariableChange` on projective models (`projModelVCIso`, the projectivisation
of `(x, y) ↦ (u²x + r, u³y + su²x + t)`), its pointedness, faithfulness — and the
**comparison theorem** (T-W7.1b, audit A1): every pointed isomorphism of projective
Weierstrass models over an arbitrary ring is induced by a unique variable change. This is the
dependency the round-1 reviewer reply missed; without it, chart-overlap agreement of the
glued group law would circularly require canonicity. It is also fix-option (3) of the prior
B2 on `isWeierstrassModel_unique` (b2_log 2026-07-07), here WITHOUT BB-RR: the proof route is
the pole filtration of `PoleFiltration.lean`.

Sources: audit A1 (`expert-review/2026-07-07-tw7/integration.md`); KM §2.2/Deligne
*Formulaire*-style statement, proof re-derived uniformly (pole filtration + freeness).
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve

universe u

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-- **(T-W7.0h-i)** The isomorphism of projective Weierstrass models induced by a variable
change `C = (u, r, s, t)`: the projectivisation of the affine coordinate change
`(x, y) ↦ (u²x + r, u³y + su²x + t)` (mathlib's `VariableChange` convention), an isomorphism
`projModel (C • W) ≅ projModel W`. Source: Silverman III.3.1(b) (projective form); the graded
ring map mirrors `baseChangeGradedHom`. -/
noncomputable def projModelVCIso (C : VariableChange R) (W : WeierstrassCurve R) :
    projModel (C • W) ≅ projModel W :=
  sorry

/-- **(T-W7.0h-i, π-compatibility)** `projModelVCIso` is a morphism over `Spec R`. -/
theorem projModelVCIso_π (C : VariableChange R) (W : WeierstrassCurve R) :
    (projModelVCIso C W).hom ≫ projModelπ W = projModelπ (C • W) := by
  sorry

/-- **(T-W7.0h-i, pointedness)** `projModelVCIso` carries the point at infinity to the point
at infinity ( `[0:1:0]` is fixed by the projectivised coordinate change). -/
theorem projModelVCIso_zero (C : VariableChange R) (W : WeierstrassCurve R) :
    projModelZero (C • W) ≫ (projModelVCIso C W).hom = projModelZero W := by
  sorry

/-- **(T-W7.0h-i, cocycle)** The model isomorphisms compose according to the
`VariableChange` group law (contravariantly on the acted curve). Source: the affine cocycle
`vcX_comp`/`vcY_comp` (`ForMathlib/AffinePointVariableChange`, DONE), projectivised. -/
theorem projModelVCIso_mul (C C' : VariableChange R) (W : WeierstrassCurve R) :
    (projModelVCIso (C * C') W).hom =
      (eqToHom (by rw [mul_smul])) ≫ (projModelVCIso C (C' • W)).hom ≫
        (projModelVCIso C' W).hom := by
  sorry

/-- **(T-W7.1b, main — the comparison theorem)** Every isomorphism of projective Weierstrass
models over a ring `R` that respects the structure morphisms and the points at infinity is
induced by a variable change: there is a `C : VariableChange R` with `C • W = W'`, and `e` is
the transport of `projModelVCIso` along that equality. The proof route is the pole filtration:
a pointed iso preserves the affine part (`projModel_hom_ext_of_affine` territory) and the
filtration `F_n`, whose low-degree freeness forces `Φ(x') = αx + β`, `Φ(y') = γy + δx + ε`
with `α, γ` units; matching the two Weierstrass relations forces `α³ = γ²`, and
`u := γ/α` yields `C`. Source: audit A1; KM §2.2-style; prior-B2 fix-option (3). -/
theorem pointedIso_exists_variableChange (W W' : WeierstrassCurve R)
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    ∃ C : VariableChange R, ∃ hW : C • W' = W,
      e.hom = eqToHom (by rw [← hW]) ≫ (projModelVCIso C W').hom := by
  sorry

/-- **(T-W7.1b, uniqueness — faithfulness of the model action)** The variable change inducing
a given pointed model isomorphism is unique: distinct variable changes with the same action on
`W` induce distinct model isomorphisms. (Uniqueness is NOT "C with C • W' = W is unique" —
automorphisms exist for special `W`; it is the pinning by the induced isomorphism.) Source:
audit A1 (b5); the filtration argument reads `(u, r, s, t)` off `Φ(x'), Φ(y')`. -/
theorem projModelVCIso_injective (C₁ C₂ : VariableChange R) (W : WeierstrassCurve R)
    (hW : C₁ • W = C₂ • W)
    (h : (projModelVCIso C₁ W).hom = eqToHom (by rw [hW]) ≫ (projModelVCIso C₂ W).hom) :
    C₁ = C₂ := by
  sorry

end ModularCurves
