import ModularCurves.Moduli.Representability
import ModularCurves.Moduli.Groupoid
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# General level structures P_H, and full level N over an arbitrary base

The level-uniform layer, answering "what about other levels, and full level N?"
concretely (owner question, 2026-07-05; Loeffler §3.8; KM Ch. 3–5, 7).

## Contents

* The `GL₂(ℤ/N)`-action on full level structures (a full level structure is an
  isomorphism `(ℤ/N)² ≅ E[N]`; the group acts by precomposition — in the `(P,Q)`
  coordinates `g • (P,Q) = (g₁₁P + g₂₁Q, g₁₂P + g₂₂Q)`).
* For each subgroup `H ≤ GL₂(ℤ/N)`, the moduli problem `P_H` of `H`-orbits of full
  level structures (Loeffler Fact 3.8.1, verbatim: "`P_H(E/k̄) = {H`-orbits of
  isomorphisms `(ℤ/N)² ≅ E[N]}`"), specialising to `Γ(N)` (`H = 1`), `Γ₁(N)`
  (`H = {(1 *; 0 *)}`), `Γ₀(N)` (`H = {(* *; 0 *)}`).
* **Relative representability of `P_H`** (Loeffler Prop 3.8.2, verbatim: "P_H is
  relatively representable and étale over `Ell/ℤ[1/N]` … For `H = {1}` … it is an open
  subscheme of `E[N] ×_S E[N]` given by non-vanishing of Weil pairings. For general
  `H` just take the quotient of this by `H`.").
* **The rigidity criterion** (Loeffler Prop 3.8.3, verbatim: "`P_H` is rigid on
  `Ell/R[1/6]` if and only if the preimage in `SL₂(ℤ)` of `H ∩ SL₂(ℤ/N)` contains no
  elements of finite order (i.e. has no elliptic points and does not contain `−1`)").
* **Fine modular curves of arbitrary level**: rigid ⟹ representable, smooth over
  `ℤ[1/N]` (Loeffler §3.8: "there is a scheme `Y = Y_{P_H}` … One can check that
  `Y_{P_H}` is smooth over `ℤ[1/N]`").
* **Full level N over an arbitrary base (Drinfeld form)** and its representability for
  `N ≥ 3` over any ring — KM 4.7.2/5.1 territory (⧗KM: do-not-formalize-from-memory;
  statement here, closure gated on the full text). This is "full level N over ℤ".
* **The honest stack content at small N**: for `N ≤ 2` the set-valued problem is NOT
  rigid (`[-1]` acts trivially on `E[2]`), so there is no fine scheme — the object of
  record is the levelled groupoid (`FullLevelGroupoid`), per design D6. Coarse spaces:
  `Moduli/Coarse.lean`.
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

variable {S : Scheme.{u}}

namespace EllipticCurve

/-- A (naive) full level-`N` point: a pair of sections forming a naive full level-`N`
structure. The bundled object on which `GL₂(ℤ/N)` acts. -/
def FullLevelPt (E : EllipticCurve S) (N : ℕ) [NeZero N] : Type u :=
  { PQ : E.Section × E.Section // E.IsNaiveFullLevel N PQ.1 PQ.2 }

variable (E : EllipticCurve S)

/-- The `GL₂(ℤ/N)`-action on full level structures, by precomposition of the
isomorphism `(ℤ/N)² ≅ E[N]`: in coordinates,
`g • (P, Q) = (g₁₁·P + g₂₁·Q, g₁₂·P + g₂₂·Q)` (entries lifted via `ZMod.val`;
well-defined because level points are killed by `N`). Membership preservation is
`T-H2`. Source: Loeffler Fact 3.8.1 ("H-orbits of isomorphisms (ℤ/N)² ≅ E[N]"). -/
noncomputable def glSmul {N : ℕ} [NeZero N]
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : E.FullLevelPt N) :
    E.FullLevelPt N :=
  let m : Matrix (Fin 2) (Fin 2) (ZMod N) := g
  ⟨((((m 0 0).val : ℤ) • L.1.1 + ((m 1 0).val : ℤ) • L.1.2,
     ((m 0 1).val : ℤ) • L.1.1 + ((m 1 1).val : ℤ) • L.1.2)),
    by sorry⟩

/-- **(T-H2a)** The action law `(g * h) • L = g • (h • L)` (uses that level points are
killed by `N`, so the `ZMod.val` lifts compose correctly mod `N`). -/
theorem glSmul_mul {N : ℕ} [NeZero N]
    (g h : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : E.FullLevelPt N) :
    E.glSmul (g * h) L = E.glSmul g (E.glSmul h L) := by sorry

/-- The `H`-orbit equivalence on full level structures, for `H ≤ GL₂(ℤ/N)`. -/
noncomputable def hOrbitSetoid {N : ℕ} [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) :
    Setoid (E.FullLevelPt N) :=
  ⟨fun L L' => ∃ g ∈ H, E.glSmul g L = L', by sorry⟩

end EllipticCurve

section GammaH

variable (R : CommRingCat.{u})

/-- **The moduli problem `P_H`** for `H ≤ GL₂(ℤ/N)`: `E/S ↦ {H`-orbits of (naive) full
level-`N` structures on `E/S}`. Specialisations: `H = ⊥` is `[Γ(N)]`-naive
(`gammaHNaive_bot`); `H = {(1 *; 0 *)}` is `[Γ₁(N)]`; `H = {(* *; 0 *)}` is
`[Γ₀(N)]` (upper-triangular Borel). Source: Loeffler Fact 3.8.1; KM Ch. 3 + 7 (the
quotient presentation, ⧗KM for closure). Functor laws and orbit-compatibility of
section-pullback are `T-H3`. -/
noncomputable def gammaHNaiveProblem (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) : ModuliProblem R where
  obj X := Quotient (X.unop.curve.hOrbitSetoid H)
  map f := ↾Quotient.map
    (fun L => ⟨⟨EllHom.pullSection R f.unop L.1.1, EllHom.pullSection R f.unop L.1.2⟩,
      by sorry⟩)
    (by sorry)
  map_id := by sorry
  map_comp := by sorry

/-- **(T-H1)** `P_⊥` is the naive full-level problem: the `H = ⊥` orbits are
singletons, recovering `gammaFullNaiveProblem`. -/
theorem gammaHNaive_bot (N : ℕ) [NeZero N] :
    Nonempty ((gammaHNaiveProblem R N ⊥) ≅ gammaFullNaiveProblem R N) := by sorry

/-- **(T-H4 = Loeffler Prop 3.8.2)** `P_H` is relatively representable and étale over
`Ell/R` when `N` is invertible: for every `E/S`, the functor `T ↦ P_H(E ×_S T)` is
representable by a scheme finite étale over `S`. (Proof route for `H = {1}`: the open
subscheme of `E[N] ×_S E[N]` cut by non-vanishing of Weil pairings — consumes
workstream C; for general `H`: the quotient by `H` — consumes stream Q.) -/
theorem gammaHNaive_relativelyRepresentable (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R)) :
    (gammaHNaiveProblem R N H).RelativelyRepresentable := by sorry

/-- **(T-H5 = Loeffler Prop 3.8.3, the rigidity criterion for arbitrary level)** Over
`R` with `6N` invertible: `P_H` is rigid iff the preimage of `H` in `SL₂(ℤ)` is
torsion-free ("contains no elements of finite order — i.e. has no elliptic points and
does not contain `−1`"). -/
theorem gammaHNaive_rigid_iff (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit ((6 * N : ℕ) : R)) :
    (gammaHNaiveProblem R N H).Rigid ↔
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        (Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ) ∈ H) →
        IsOfFinOrder γ → γ = 1 := by sorry

/-- **(T-H6, fine modular curves of arbitrary level)** For rigid `P_H` (and `N`
invertible), `P_H` is representable — "there is a scheme `Y = Y_{P_H}`, an elliptic
curve `ℰ/Y` and an `α ∈ P_H(ℰ/Y)` representing the functor" — and the base is smooth
and affine over `Spec R`. Every fine modular curve of every level arises here.
Source: Loeffler §3.8 (after 3.8.3); via `representable_iff` (T-E5) + T-H4. -/
theorem gammaHNaive_representable_of_rigid (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R)) (hrig : (gammaHNaiveProblem R N H).Rigid) :
    (gammaHNaiveProblem R N H).Representable := by sorry

/-- **(T-H7, the honest stack statement at small `N`)** For `N ≤ 2` the full-level
problem is NOT rigid — `[-1]` is a nontrivial automorphism acting trivially on all
level data (on `E[2]`, `−P = P`) — so no fine scheme exists and the object of record
is the levelled groupoid (design D6). This is the precise sense in which "for full
level `N ≤ 2` we only get a stack". -/
theorem gammaFullNaive_not_rigid_of_le_two (N : ℕ) [NeZero N] (hN : N ≤ 2)
    (hR : Nonempty (EllObj R)) :
    ¬ (gammaFullNaiveProblem R N).Rigid := by sorry

end GammaH

section DrinfeldOverZ

variable (R : CommRingCat.{u})

/-- **Full level N over an arbitrary base — the Drinfeld form.** The moduli problem
`E/S ↦ {Drinfeld full level-N structures}` (KM 3.1: pairs with `Σ [aP+bQ] = E[N]` as
divisors), with NO invertibility hypothesis on `N`. Over `ℤ[1/N]`-schemes it agrees
with the naive problem (T-D8); at primes dividing `N` it is the correct object.
Functor laws `T-H8a`. Source: KM 3.1 ⧗ (statement via [Loe]/KM-Ch.1 machinery, which
is fully sourced). -/
noncomputable def gammaFullDrinfeldProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { PQ : X.unop.curve.Section × X.unop.curve.Section //
    X.unop.curve.IsFullLevel N PQ.1 PQ.2 }
  map f := ↾fun PQ => ⟨⟨EllHom.pullSection R f.unop PQ.1.1,
    EllHom.pullSection R f.unop PQ.1.2⟩, by sorry⟩
  map_id := by sorry
  map_comp := by sorry

/-- The Drinfeld `Γ₁(N)` problem over an arbitrary base: points of exact order `N`
(KM 3.2 via KM 1.4.1 — fully sourced Ch. 1 machinery). -/
noncomputable def gammaOneDrinfeldProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { P : X.unop.curve.Section // X.unop.curve.IsGammaOne N P }
  map f := ↾fun P => ⟨EllHom.pullSection R f.unop P.1, by sorry⟩
  map_id := by sorry
  map_comp := by sorry

/-- **(T-H8 = KM 4.7.2/5.1 — "full level N over ℤ" — ⧗KM, closure gated on the full
text)** For `N ≥ 3`, the Drinfeld full-level problem is rigid and representable over
an **arbitrary** ring — no invertibility of `N`. (KM: `Y(N)` is an affine scheme,
flat and finite over the `j`-line over `ℤ`, regular; those refinements are phase-2
statements to be cut verbatim when the full text lands.) -/
theorem gammaFullDrinfeld_representable (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    (gammaFullDrinfeldProblem R N).Rigid ∧
      (gammaFullDrinfeldProblem R N).Representable := by sorry

/-- **(T-H9 = KM 5.x for `Γ₁` — ⧗KM)** For `N ≥ 4`, the Drinfeld `Γ₁(N)` problem is
rigid and representable over an arbitrary ring ("`Y₁(N)` over `ℤ`"). -/
theorem gammaOneDrinfeld_representable (N : ℕ) [NeZero N] (hN : 4 ≤ N) :
    (gammaOneDrinfeldProblem R N).Rigid ∧
      (gammaOneDrinfeldProblem R N).Representable := by sorry

end DrinfeldOverZ

namespace EllipticCurve

/-- The **levelled groupoid**: elliptic curves over `S` with (naive) full level-`N`
structure; morphisms are pointed `S`-isomorphisms carrying one level structure to the
other. For `N ≥ 3` this groupoid is discrete on isomorphism classes
(`aut_trivial_of_fullLevel`); for `N ≤ 2` it is the object of record — the value at
`S` of the moduli **stack** of full level-`N` structures
(`gammaFullNaive_not_rigid_of_le_two`). -/
structure LevelledHom {N : ℕ} [NeZero N]
    (X Y : Σ E : EllipticCurve S, E.FullLevelPt N) where
  hom : X.1 ⟶ Y.1
  level_w₁ : X.2.1.1.1 ≫ hom.hom = Y.2.1.1.1
  level_w₂ : X.2.1.2.1 ≫ hom.hom = Y.2.1.2.1

noncomputable instance fullLevelGroupoid (N : ℕ) [NeZero N] :
    Category (Σ E : EllipticCurve S, E.FullLevelPt N) where
  Hom := LevelledHom
  id X := ⟨𝟙 X.1, by sorry, by sorry⟩
  comp f g := ⟨f.hom ≫ g.hom, by sorry, by sorry⟩
  id_comp := by intros; sorry
  comp_id := by intros; sorry
  assoc := by intros; sorry

end EllipticCurve

end ModularCurves
