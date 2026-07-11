import ModularCurves.Moduli.Representability
import ModularCurves.Moduli.PullSectionCanonicity

/-!
# The naive level-structure moduli problems (relocated holder, Y1-CLOSER S4)

Relocated byte-identical from `Moduli/Representability.lean` (pointer there; v10.117
doctrine) so the three parked `sorry`s can consume A's `PullSectionCanonicity.lean` per its
wiring note: `pullSection_add` := the finite-presentation transport; the functor-law
memberships close by the killing-clause transport (`pullSection_zsmul_of_finitePresentation`)
plus the barehanded fibrewise `Point.pull`-compatibility. Everything bottoms out at the
single designed primitive `isMonHom_of_one_comp_eq'_of_finitePresentation` (route (a)
`RigiditySpreadingOut` / route (c) T-W7a — in flight on other lanes).
-/

open AlgebraicGeometry CategoryTheory Polynomial

universe u

namespace ModularCurves

section LevelModuli

variable (R : CommRingCat.{u})

/-- **(T-E4a, additivity of section-pullback — surfaced by the adversarial pass
2026-07-06)** `pullSection` is a group homomorphism. NOT free: `EllHom` carries no
group-compatibility field and the two curves' `grp` data are independent, so this
consumes uniqueness of the group law with given unit (`abelEnrichment_unique`,
GME Cor 2.2.5 — a pointed isomorphism onto the pullback is automatically a group
isomorphism). Every moduli-functor `map` below (Γ₁/Γ(N)/P_H, naive and Drinfeld)
consumes this lemma; it restores the dependency edge from the level functors to the
canonicity chain A6.δ that the earlier "nothing depends on it" amendment dropped. -/
theorem EllHom.pullSection_add {X Y : EllObj R} (f : X ⟶ Y)
    (P Q : Y.curve.Section) :
    EllHom.pullSection R f (P + Q) =
      EllHom.pullSection R f P + EllHom.pullSection R f Q := by sorry

/-- The naive `Γ₁(N)` moduli problem over `R`: `E/S ↦ {P ∈ E(S) : P` has naive exact
order `N}` (fibrewise; the right notion for `N` invertible, KM 1.4.4). Functor laws are
`T-E4`. Source: Loeffler §3.3/§3.8; KM 3.2 + 3.7. -/
noncomputable def gammaOneNaiveProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { P : X.unop.curve.Section // X.unop.curve.IsNaiveGammaOne N P }
  map f := ↾fun P => ⟨EllHom.pullSection R f.unop P.1, by sorry⟩
  map_id X := by
    ext P
    exact congrArg Subtype.val (EllHom.pullSection_id R P.1)
  map_comp f g := by
    ext P
    exact congrArg Subtype.val (EllHom.pullSection_comp R g.unop f.unop P.1)

/-- The naive full-level-`N` (`Γ(N)`) moduli problem over `R`:
`E/S ↦ {(P, Q) generating E[N] in every fibre}`. Source: Loeffler Fact 3.8.1 (verbatim:
"pairs of sections `P, Q ∈ E[S]` generating `E[N]` in every fibre"); KM 3.1 + 3.7. -/
noncomputable def gammaFullNaiveProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { PQ : X.unop.curve.Section × X.unop.curve.Section //
    X.unop.curve.IsNaiveFullLevel N PQ.1 PQ.2 }
  map f := ↾fun PQ => ⟨⟨EllHom.pullSection R f.unop PQ.1.1,
    EllHom.pullSection R f.unop PQ.1.2⟩, by sorry⟩
  map_id X := by
    ext PQ
    · exact congrArg Subtype.val (EllHom.pullSection_id R PQ.1.1)
    · exact congrArg Subtype.val (EllHom.pullSection_id R PQ.1.2)
  map_comp f g := by
    ext PQ
    · exact congrArg Subtype.val (EllHom.pullSection_comp R g.unop f.unop PQ.1.1)
    · exact congrArg Subtype.val (EllHom.pullSection_comp R g.unop f.unop PQ.1.2)

/-- **(T-E7 = Loeffler Thm 3.4.4 + Def 3.3.6; KM 5.x for the Drinfeld upgrade)** For
`N ≥ 4` and `N` invertible in `R`, the naive `Γ₁(N)` problem is representable, and the
representing base scheme is smooth and affine over `Spec R`.
Loeffler (verbatim, Thm 3.4.4): "`Y₁(N)_{ℤ[1/N]}` is smooth over `ℤ[1/N]`."

Notes (adversarial pass 2026-07-06): TRUE only after `IsNaiveGammaOne` gained its
global killing clause (without it a `ℚ̄[ε]`-family gave pro-representation
`ℚ̄[[t,s]]`, contradicting smooth + quasi-finite-over-j). General `R` follows from
`ℤ[1/N]` by base change (`Smooth`, `IsAffineHom` stable). Affineness for general `N`
is QUOTE-PARTIAL: Loeffler's `Spec` display is verbatim only for `N = 5`; attach the
KM affine-over-the-j-line locator when the full text lands. -/
theorem gammaOneNaive_representable (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    (gammaOneNaiveProblem R N).Representable ∧
      ∀ X : EllObj R, Nonempty ((gammaOneNaiveProblem R N).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) := by sorry

/-- **(T-E9 = Loeffler Prop 3.8.2–3.8.3; KM 3.1/4.7/5.1)** For `N ≥ 3` and `N` invertible
in `R`, the naive full-level problem `[Γ(N)]` is rigid and representable; the representing
scheme `Y(N)` is smooth and affine over `Spec R`.
(Rigidity: Loeffler Prop 3.8.3 covers `Ell/R[1/6]` only; for residue characteristics
2 and 3 the source of record is the GME 2.6.4 Aut-computation ("`ε ∈ Aut(E,φ)`,
`n ≥ 3` invertible ⟹ `ε = 1`", chain B9 in decomposition-gme2 — valid in all
characteristics with `N` invertible); KM locator pending. Smooth+affine conjunct
restored 2026-07-06 — it was in this docstring but missing from the statement.) -/
theorem gammaFullNaive_representable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) :
    ((gammaFullNaiveProblem R N).Rigid ∧ (gammaFullNaiveProblem R N).Representable) ∧
      ∀ X : EllObj R, Nonempty ((gammaFullNaiveProblem R N).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) := by
  sorry

end LevelModuli

end ModularCurves
