import ModularCurves.EllipticCurve.GroupLaw
import ModularCurves.EllipticCurve.Torsion

/-!
# The endomorphism ring, degree, and Hasse bound of `E/S` (KM Ch. 2, §§2.5–2.7)

The `End(E/S)` / degree / Hasse layer feeding rigidity (`aut_hom_eq_id_of_fullLevel`,
`Moduli/Groupoid.lean`). `End(E/S)` is the ring of `Over S`-endomorphisms
`E.asOver ⟶ E.asOver`: its additive group is the (multiplicatively-spelled) `Hom.commGroup`
(group-`1` = zero morphism = ring `0`, group-`*` = pointwise sum = ring `+`, `f ^ n` = `[n]·f`,
`E.mulBy n = (𝟙 E.asOver) ^ n = [n]`); ring-`1` = `𝟙 E.asOver`; ring-`*` = composition `≫`.

**This file is a `/develop --decompose` skeleton** (T-END0, tickets.md §v10.5): the degree, dual
isogeny and trace are stated as DATA sorries governed by the DATA-SORRY REGISTER (their KM sources
are in the docstrings, their construction tickets are T-END0b, and the pins below are their
specification lemmas — downstream code may use them only through those). The leaf theorems
T-G3b/c/d/e are `theorem`-level sorries. Full plan + verbatim KM quotes:
`.mathlib-quality/decomposition-end0.md`.

Sources (KM, verbatim in the decl docstrings): 2.5.1 (pointed ⟹ hom; dual via Abel), 2.6.1
(`f^t f = [deg f]`), 2.6.1.1 (`deg[N] = N²`, `f^{tt} = f`), 2.6.2 (dual additive), 2.6.2.2 (trace),
2.6.3 (char.-poly + `(tr f)² ≤ 4 deg f`), 2.7.2 (rigidity of level `N`). Fibre anchor for T-G3c:
HasseWeil `Foundation/DegreeQuadraticForm.lean` + `HasseBound.lean` (IMPORT at execution).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **DS-data (T-END0b — KM 2.6.1)** The degree `deg : End(E/S) → ℤ`. KM (verbatim, Thm 2.6.1):
*"f^t f = deg(f) := { N if f is an isogeny of degree N; 0 if f = 0 }."* Pinned by
`endDual_comp_self`, `endDeg_mulBy`. -/
noncomputable def endDeg (f : E.asOver ⟶ E.asOver) : ℤ := sorry

/-- **DS-data (T-END0b — KM 2.5/2.6.1)** The dual (transpose) isogeny `f ↦ f^t`. KM (verbatim,
proof of 2.5.1, print p.79): *"f^t = Pic(f) = f^* : Pic⁰_{E′/S} → Pic⁰_{E/S} … via Abel's
isomorphism … an S-homomorphism f^t : E′ → E."* Pinned by `endDual_comp_self`, `endDual_mulBy`. -/
noncomputable def endDual (f : E.asOver ⟶ E.asOver) : E.asOver ⟶ E.asOver := sorry

/-- **DS-data (T-END0d — KM 2.6.2.2)** The trace `tr : End(E/S) → ℤ`. KM (verbatim, Cor 2.6.2.2):
*"there exists an integer, called trace(f), such that f + f^t = trace(f)."* Pinned by
`endTrace_spec`. -/
noncomputable def endTrace (f : E.asOver ⟶ E.asOver) : ℤ := sorry

/-- **(T-END0b pin — KM 2.6.1)** The defining identity of the degree: `f^t ∘ f = [deg f]`. -/
theorem endDual_comp_self (f : E.asOver ⟶ E.asOver) :
    E.endDual f ≫ f = E.mulBy (E.endDeg f) := sorry

/-- **(T-END0c — KM 2.6.1.1)** `deg [N] = N²` (KM: *"deg([N]) = N²"*, displayed in the proof of
Cor 2.6.1.1). Fibre anchor: HasseWeil `mulByInt_degree` (BB-DEG) via T-B6. -/
theorem endDeg_mulBy (n : ℤ) : E.endDeg (E.mulBy n) = n ^ 2 := sorry

/-- **(KM 2.6.2.1)** The transpose of `[N]` is `[N]` itself: `[N]^t = [N]`. -/
theorem endDual_mulBy (n : ℤ) : E.endDual (E.mulBy n) = E.mulBy n := sorry

/-- **(T-END0d pin — KM 2.6.2.2)** The trace identity `f + f^t = [tr f]` (`*` is the endomorphism
addition, the pointwise `Hom.commGroup` operation). -/
theorem endTrace_spec (f : E.asOver ⟶ E.asOver) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    f * E.endDual f = E.mulBy (E.endTrace f) := sorry

/-- **(T-G3b — KM 2.6.3 / 2.7.2 proof)** The degree quadratic expansion
`deg(1 + g∘[N]) = 1 + N·tr g + N²·deg g`. Here `1 = 𝟙 E.asOver` (identity endomorphism), `+` is
the pointwise `Hom.commGroup` operation `*`, and `g∘[N] = g ≫ [N]`. KM (verbatim, proof of Cor
2.7.2): *"ε = 1 + gN, so … deg(ε) = 1 + N trace(g) + N² deg(g)."* -/
theorem endDeg_one_add_mulBy_comp (n : ℤ) (g : E.asOver ⟶ E.asOver) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    E.endDeg (𝟙 E.asOver * (g ≫ E.mulBy n)) =
      1 + n * E.endTrace g + n ^ 2 * E.endDeg g := sorry

/-- **(T-G3c — KM 2.6.3(2))** The discriminant / Hasse–Cauchy–Schwarz bound `(tr g)² ≤ 4·deg g`.
KM (verbatim, Thm 2.6.3(2)): *"(trace(f))² ≤ 4 deg(f)"*, proof *"deg(n − mf) ≥ 0."* Fibrewise via
T-RED0 + HasseWeil `hasse_bound` / `degree_quadratic_closed` transfer (IMPORT, never re-prove). -/
theorem endTrace_sq_le (g : E.asOver ⟶ E.asOver) :
    E.endTrace g ^ 2 ≤ 4 * E.endDeg g := sorry

/-- **(T-G3e — KM 2.6.3(2) proof)** Positive-definiteness of `deg`: `deg g = 0 ⟹ g = 0` (here the
zero endomorphism is `[0] = E.mulBy 0`). KM's `deg(n − mf) ≥ 0` sharpened to definiteness for the
endomorphism ring of an elliptic curve. -/
theorem eq_zero_of_endDeg_eq_zero (g : E.asOver ⟶ E.asOver) (hg : E.endDeg g = 0) :
    g = E.mulBy 0 := sorry

/-- **(T-G3d — KM 2.7.2 proof)** `N`-divisibility of `ε − 1`: an endomorphism `ε` fixing the
`N`-torsion subscheme `E[N]` (i.e. `ε.left` restricts to the identity on `E.torsionι N`) factors as
`ε = 1 + g∘[N]` for some `g ∈ End(E/S)`. KM (verbatim, proof of Cor 2.7.2): *"ε−1 kills E[N], so it
factors as ε−1 = g·N for some g ∈ End(E). Then ε = 1 + gN."* (`1 = 𝟙 E.asOver`, `+` = `Hom.commGroup`
`*`, `g∘[N] = g ≫ [N]`.) -/
theorem exists_eq_one_add_mulBy_comp_of_fixesTorsion (N : ℕ) [NeZero N]
    (ε : E.asOver ⟶ E.asOver) (hfix : E.torsionι N ≫ ε.left = E.torsionι N) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    ∃ g : E.asOver ⟶ E.asOver, ε = 𝟙 E.asOver * (g ≫ E.mulBy (N : ℤ)) := sorry

end EllipticCurve

end ModularCurves
