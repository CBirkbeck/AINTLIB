/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.GroupLaw
import ModularCurves.EllipticCurve.Torsion
import ModularCurves.EllipticCurve.Rigidity

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

/-- **(T-END0a foundation — KM 2.5.1, PROVEN via `isMonHom_of_one_comp_eq'`)** Over a locally
noetherian base, a **pointed** endomorphism of `E/S` (one fixing the group unit / zero section)
is a monoid homomorphism: `μ ≫ f = (f ⊗ f) ≫ μ`. This is the additivity underlying the ring
structure on `End(E/S)` (postcomposition by such `f` distributes over the pointwise group law).
The `[IsLocallyNoetherian S]` hypothesis drops out when T-W7.8 (EGA IV §8 spreading-out) lands,
per the T-E4a-noeth future-proofing pattern. KM (verbatim, Thm 2.5.1): *"any S-morphism
f : E → E′ with f(0) = 0 is a homomorphism."* Reuses the sorry-free T-W7.7 rigidity engine
(`isMonHom_of_one_comp_eq'`) + `EllipticCurveGeom.universallyOConnected`. -/
theorem endMonHom [IsLocallyNoetherian S] (f : E.asOver ⟶ E.asOver)
    (hη : η[E.asOver] ≫ f = η[E.asOver]) :
    μ[E.asOver] ≫ f = MonoidalCategory.tensorHom f f ≫ μ[E.asOver] := by
  haveI : Smooth E.π := SmoothOfRelativeDimension.smooth (n := 1) (f := E.π)
  haveI : IsProper E.asOver.hom := inferInstanceAs (IsProper E.π)
  haveI : Flat E.asOver.hom := inferInstanceAs (Flat E.π)
  haveI : IsSeparated E.asOver.hom := inferInstanceAs (IsSeparated E.π)
  exact isMonHom_of_one_comp_eq' E.toEllipticCurveGeom.universallyOConnected f hη

/-- **(T-END0a — right-distributivity of `End(E/S)`)** Post-composition by a **pointed**
endomorphism `f` distributes over the pointwise (additive) group law: `(a * b) ≫ f = (a ≫ f) * (b ≫
f)`
(the `*` is the additive `Hom.commGroup`/`Hom.group` operation). This is the additive half of the
ring structure that is *not* free — pre-composition distributes over `*` for **every** morphism
(`MonObj.comp_mul`, naturality of `lift`), but post-composition distributes only through a *monoid
homomorphism*. A pointed `f` is one (`endMonHom`), so post-composition by `f` is the bundled monoid
hom `IsMonHom.monoidHom f` and the identity is its `map_mul`. -/
theorem endPostcomp_mul [IsLocallyNoetherian S] (a b f : E.asOver ⟶ E.asOver)
    (hη : η[E.asOver] ≫ f = η[E.asOver]) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    (a * b) ≫ f = (a ≫ f) * (b ≫ f) := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  haveI : IsMonHom f := { one_hom := hη, mul_hom := endMonHom E f hη }
  exact map_mul (IsMonHom.monoidHom f E.asOver) a b

/-- The multiplication-by-`n` isogeny `[n]` is **pointed**: `η ≫ [n] = η` (it fixes the zero
section, `n • 0 = 0`). Since `[n] = (𝟙)^n` in the hom-group, pre-composition by `η` commutes with
the group power (`GrpObj.comp_zpow`), and `η` is the unit of the group `𝟙_ ⟶ E.asOver`, so
`η ≫ (𝟙)^n = (η ≫ 𝟙)^n = η^n = η`. Feeds `IsMonHom (E.mulBy n)` and the final `ε = 𝟙` step. -/
theorem mulBy_pointed (n : ℤ) : η[E.asOver] ≫ E.mulBy n = η[E.asOver] := by
  have hη1 : η[E.asOver] = (1 : 𝟙_ (Over S) ⟶ E.asOver) := by
    rw [Hom.one_def]; simp
  simp only [EllipticCurve.mulBy]
  rw [GrpObj.comp_zpow, Category.comp_id, hη1, one_zpow]

/-- `[1] = 𝟙 E.asOver`: multiplication-by-one is the identity endomorphism (`(𝟙)^1 = 𝟙`). -/
theorem mulBy_one : E.mulBy 1 = 𝟙 E.asOver := by
  simp only [EllipticCurve.mulBy, zpow_one]

/-- **(T-END0b pin — KM 2.6.1)** The defining identity of the degree: `f^t ∘ f = [deg f]`. -/
theorem endDual_comp_self (f : E.asOver ⟶ E.asOver) :
    E.endDual f ≫ f = E.mulBy (E.endDeg f) := sorry

/-- **(T-END0c — KM 2.6.1.1)** `deg [N] = N²` (KM: *"deg([N]) = N²"*, displayed in the proof of
Cor 2.6.1.1). Fibre anchor: HasseWeil `mulByInt_degree` (BB-DEG) via T-B6. -/
theorem endDeg_mulBy (n : ℤ) : E.endDeg (E.mulBy n) = n ^ 2 := sorry

/-- **(T-END0b pin — KM 2.6.1)** The degree is non-negative: `0 ≤ deg f` (KM 2.6.1 defines
`deg f = N ≥ 0` for an isogeny of degree `N`, and `deg 0 = 0`). Supplies the `0 ≤ d` hypothesis of
`gme_deg_trace_forces_zero` in the rigidity computation. -/
theorem endDeg_nonneg (f : E.asOver ⟶ E.asOver) : 0 ≤ E.endDeg f := sorry

/-- **(T-END0c pin — KM 2.6.1, `deg` multiplicative)** The degree is multiplicative under
composition: `deg(f ≫ g) = deg f · deg g`. KM (Thm 2.6.1 / Cor 2.6.1.1): the degree of a composite
isogeny is the product of the degrees (`(f∘g)^t (f∘g) = g^t (f^t f) g = [deg f][deg g]`). -/
theorem endDeg_comp (f g : E.asOver ⟶ E.asOver) :
    E.endDeg (f ≫ g) = E.endDeg f * E.endDeg g := sorry

/-- The identity endomorphism has degree `1`: `deg 𝟙 = 1` (`𝟙 = [1]` and `deg [1] = 1² = 1`).
Proved from `mulBy_one` + `endDeg_mulBy` (no data-sorry of its own). -/
theorem endDeg_one : E.endDeg (𝟙 E.asOver) = 1 := by
  rw [← E.mulBy_one, E.endDeg_mulBy, one_pow]

/-- **(deg of an automorphism = 1 — KM 2.7.1)** An invertible endomorphism (an automorphism of
`E/S`) has degree `1`. From multiplicativity `deg f · deg (f⁻¹) = deg(f ≫ f⁻¹) = deg 𝟙 = 1` and
`deg ≥ 0`, `deg f` is a non-negative integer dividing `1`, hence `1`. This discharges the
`deg ε = 1` bridge of `aut_hom_eq_id_of_fullLevel`. -/
theorem endDeg_eq_one_of_isIso (f : E.asOver ⟶ E.asOver) [IsIso f] : E.endDeg f = 1 := by
  have hmul : E.endDeg f * E.endDeg (inv f) = 1 := by
    rw [← E.endDeg_comp, IsIso.hom_inv_id, E.endDeg_one]
  have hdvd : E.endDeg f ∣ 1 := ⟨E.endDeg (inv f), hmul.symm⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
  · exact h
  · have := E.endDeg_nonneg f; omega

/-- **(KM 2.6.2.1)** The transpose of `[N]` is `[N]` itself: `[N]^t = [N]`. -/
theorem endDual_mulBy (n : ℤ) : E.endDual (E.mulBy n) = E.mulBy n := sorry

/-- **(T-END0d pin — KM 2.6.2.2)** The trace identity `f + f^t = [tr f]` (`*` is the endomorphism
addition, the pointwise `Hom.commGroup` operation). -/
theorem endTrace_spec (f : E.asOver ⟶ E.asOver) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    f * E.endDual f = E.mulBy (E.endTrace f) := sorry

/-- **(T-END0d pin — KM 2.6.2.2 proof, polarization)** The defining polarization of the trace as
the cross term of `deg` at the identity: `deg(1 + f) = 1 + deg f + tr f` (`1 = 𝟙 E.asOver`, `+` is
the `Hom.commGroup` operation `*`). KM (verbatim, proof of Cor 2.6.2.2): *"deg(1+f) = 1 + deg(f) +
(f + f^t)"*, with `f + f^t = [tr f]`. This is the bilinear-form engine of the T-G3b expansion. -/
theorem endDeg_one_add (f : E.asOver ⟶ E.asOver) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    E.endDeg (𝟙 E.asOver * f) = 1 + E.endDeg f + E.endTrace f := sorry

/-- **(T-END0c pin — KM 2.6.1.1, `deg` multiplicative)** The degree scales quadratically under
post-composition by `[n]`: `deg(g ∘ [n]) = n² · deg g`. KM (verbatim, Cor 2.6.1.1): *"deg is
multiplicative"* together with the displayed *"deg([N]) = N²"* — here `deg(g ≫ [n]) = deg g · deg
[n]
= deg g · n²`. -/
theorem endDeg_comp_mulBy (n : ℤ) (g : E.asOver ⟶ E.asOver) :
    E.endDeg (g ≫ E.mulBy n) = n ^ 2 * E.endDeg g := sorry

/-- **(T-END0d pin — KM 2.6.2, `tr` linear)** The trace scales linearly under post-composition by
`[n]`: `tr(g ∘ [n]) = n · tr g`. KM (verbatim, Thm 2.6.2): *"(f+g)^t = f^t + g^t"* (trace additive),
with `g ≫ [n] = [n] ∘ g = n • g` in `End(E/S)`, so `tr(n • g) = n · tr g`. -/
theorem endTrace_comp_mulBy (n : ℤ) (g : E.asOver ⟶ E.asOver) :
    E.endTrace (g ≫ E.mulBy n) = n * E.endTrace g := sorry

/-- **(T-G3b — KM 2.6.3 / 2.7.2 proof)** The degree quadratic expansion
`deg(1 + g∘[N]) = 1 + N·tr g + N²·deg g`. Here `1 = 𝟙 E.asOver` (identity endomorphism), `+` is
the pointwise `Hom.commGroup` operation `*`, and `g∘[N] = g ≫ [N]`. KM (verbatim, proof of Cor
2.7.2): *"ε = 1 + gN, so … deg(ε) = 1 + N trace(g) + N² deg(g)."* -/
theorem endDeg_one_add_mulBy_comp (n : ℤ) (g : E.asOver ⟶ E.asOver) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    E.endDeg (𝟙 E.asOver * (g ≫ E.mulBy n)) =
      1 + n * E.endTrace g + n ^ 2 * E.endDeg g := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  rw [E.endDeg_one_add (g ≫ E.mulBy n), E.endDeg_comp_mulBy n g, E.endTrace_comp_mulBy n g]
  ring

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
factors as ε−1 = g·N for some g ∈ End(E). Then ε = 1 + gN."* (`1 = 𝟙 E.asOver`, `+` =
`Hom.commGroup`
`*`, `g∘[N] = g ≫ [N]`.) -/
theorem exists_eq_one_add_mulBy_comp_of_fixesTorsion (N : ℕ) [NeZero N]
    (ε : E.asOver ⟶ E.asOver) (hfix : E.torsionι N ≫ ε.left = E.torsionι N) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    ∃ g : E.asOver ⟶ E.asOver, ε = 𝟙 E.asOver * (g ≫ E.mulBy (N : ℤ)) := sorry

/-- **(T-G3a — engine core; GME 2.6.4 arithmetic, p. 151)** The purely number-theoretic heart of
the automorphism-rigidity computation, abstracted from the elliptic-curve setup so it is proved and
reused independently of the endomorphism-degree infrastructure.

Reading `d = deg g ≥ 0`, `t = tr g` (the polar/trace form of the degree quadratic form), `n = N ≥
3`:
GME's chain "`1 = deg ε = 1 + n·tr g + n²·deg g`" for an automorphism `ε = 1 + n·g` gives the linear
relation `hlin` (`n·t + n²·d = 0`), and the Hasse / Cauchy–Schwarz discriminant bound `t² ≤ 4·d`
gives `hbound`. Together with `n ≥ 3` these force `deg g = 0`, whence (by positive-definiteness of
`deg`, supplied by the caller) `g = 0` and `ε = 1`. This is the step that makes `N ≥ 3` the sharp
threshold: cancelling `n` gives `t = -n·d`, so `n²·d² ≤ 4·d`, i.e. `d·(n²·d - 4) ≤ 0`; the only
non-negative integer solution once `n² ≥ 9` is `d = 0`. Reused by `T-H5`. -/
theorem gme_deg_trace_forces_zero {n t d : ℤ} (hn : 3 ≤ n) (hd : 0 ≤ d)
    (hlin : n * t + n ^ 2 * d = 0) (hbound : t ^ 2 ≤ 4 * d) : d = 0 := by
  have hn0 : (0 : ℤ) < n := by linarith
  -- Cancel `n` from the linear relation: `t = -(n·d)`.
  have ht : t + n * d = 0 := by
    have key : n * (t + n * d) = 0 := by linear_combination hlin
    exact (mul_eq_zero.mp key).resolve_left (ne_of_gt hn0)
  have htd : t = -(n * d) := by linarith
  -- Feed `t = -(n·d)` into the discriminant bound: `n²·d² ≤ 4·d`.
  have hb2 : n ^ 2 * d ^ 2 ≤ 4 * d := by
    have h := hbound; rw [htd] at h; nlinarith [h]
  -- `n ≥ 3` and `d ≥ 0` (integer) force `d = 0`.
  by_contra hne
  have hd1 : 1 ≤ d := by omega
  nlinarith [hb2, mul_nonneg (by linarith : (0 : ℤ) ≤ n - 3) (by linarith : (0 : ℤ) ≤ n + 3),
    mul_nonneg hd (sub_nonneg.mpr hd1), hd1, sq_nonneg d]

/-- **(T-G3 core — KM 2.7.2(1), the arithmetic-geometric heart of rigidity)** An endomorphism `ε`
of `E/S` that has **degree `1`** (i.e. is an automorphism) and **fixes the `N`-torsion** `E[N]`
(`N ≥ 3`) is the identity `𝟙 E.asOver`. This is the whole `deg`/Hasse computation of KM's rigidity
corollary, assembled in `End(E/S)`-language from the leaves: T-G3d factors `ε = 1 + g∘[N]`; T-G3b
expands `deg ε = 1 + N·tr g + N²·deg g`, so `deg ε = 1` forces the linear relation `N·tr g +
N²·deg g = 0`; with `deg g ≥ 0` (`endDeg_nonneg`), the Hasse bound `tr(g)² ≤ 4·deg g` (T-G3c) and
`N ≥ 3`, the proven `gme_deg_trace_forces_zero` yields `deg g = 0`; positive-definiteness (T-G3e)
gives `g = [0]`, and `[0] ∘ [N] = [0]` (via `mulBy_pointed`) collapses `ε = 1 + [0] = 𝟙`. The
scheme-morphism form `aut_hom_eq_id_of_fullLevel` (`Moduli/Groupoid.lean`) applies this through the
pointed/automorphism/level-structure bridges. KM (verbatim, Cor 2.7.2(1)): *"If N ≥ 3, then
ε = id."* -/
theorem aut_endo_eq_one [IsLocallyNoetherian S] (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (ε : E.asOver ⟶ E.asOver) (hdeg : E.endDeg ε = 1)
    (hfix : E.torsionι N ≫ ε.left = E.torsionι N) :
    ε = 𝟙 E.asOver := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  obtain ⟨g, hg⟩ := E.exists_eq_one_add_mulBy_comp_of_fixesTorsion N ε hfix
  have hexp := E.endDeg_one_add_mulBy_comp (N : ℤ) g
  rw [← hg, hdeg] at hexp
  have hlin : (N : ℤ) * E.endTrace g + (N : ℤ) ^ 2 * E.endDeg g = 0 := by linarith
  have hdz : E.endDeg g = 0 :=
    gme_deg_trace_forces_zero hN (E.endDeg_nonneg g) hlin (E.endTrace_sq_le g)
  have hg0 : g = E.mulBy 0 := E.eq_zero_of_endDeg_eq_zero g hdz
  have h0 : E.mulBy (0 : ℤ) = (1 : E.asOver ⟶ E.asOver) := by
    simp only [EllipticCurve.mulBy, zpow_zero]
  have h1c : (1 : E.asOver ⟶ E.asOver) ≫ E.mulBy (N : ℤ) = 1 := by
    rw [Hom.one_def, Category.assoc, E.mulBy_pointed]
  rw [hg, hg0, h0, h1c, _root_.mul_one]

end EllipticCurve

end ModularCurves
