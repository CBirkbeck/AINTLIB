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
* **Full level N over an arbitrary base (Drinfeld form)**: the problem is defined
  with no invertibility hypothesis (that is the point of the Drinfeld register), and
  its representability is stated for `N ≥ 3` **with `N` invertible** (GME Thm 2.6.8
  scope). The over-ℤ refinement is KM 4.7.2/5.1 territory (⧗KM) — NOT stated here:
  the bare over-ℤ form is false (supersingular `(0,0)` in char `p ∣ N` is a Drinfeld
  structure fixed by `[-1]`), and GME's in-hand over-ℤ Aut-triviality needs coprime
  `m, n ≥ 3` dividing `N`. Cut the over-ℤ statements verbatim when the full KM text
  lands.
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

/-- **(T-H2a)** The action law. `glSmul` is *precomposition* of the trivialisation
`(ℤ/N)² ≅ E[N]` with `g`, hence a **right** action: `(φ∘g)∘h = φ∘(g*h)` reads
`(g*h) • L = h • (g • L)`. (Uses that level points are killed by `N`, so the
`ZMod.val` lifts compose correctly mod `N`.)

ADVERSARIAL FIX (2026-07-06): the previous left-action law `(g*h) • L = g • (h • L)`
was FALSE — by `Matrix.mul_apply` it asserts `(g*h) • L = (h*g) • L` for all `g, h`,
refuted on any honest basis of `E[N](ℂ)` by `g = (1 1; 0 1)`, `h = (1 0; 1 1)`.
H-orbits are unaffected (right orbits = left orbits as partitions). -/
theorem glSmul_mul {N : ℕ} [NeZero N]
    (g h : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : E.FullLevelPt N) :
    E.glSmul (g * h) L = E.glSmul h (E.glSmul g L) := by sorry

/-- The `H`-orbit equivalence on full level structures, for `H ≤ GL₂(ℤ/N)`. -/
noncomputable def hOrbitSetoid {N : ℕ} [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) :
    Setoid (E.FullLevelPt N) :=
  ⟨fun L L' => ∃ g ∈ H, E.glSmul g L = L', by sorry⟩

/-- Pull a full level point back along a base morphism `σ : T' ⟶ T`: the level of the
base-changed curve. (Membership Prop is `T-H2b`.) -/
noncomputable def FullLevelPt.pullAlong {T T' : Scheme.{u}} {E : EllipticCurve T}
    {N : ℕ} [NeZero N] (σ : T' ⟶ T) (L : E.FullLevelPt N) :
    (E.baseChange σ).FullLevelPt N :=
  ⟨(EllipticCurve.Point.asSection E σ
      ⟨σ ≫ L.1.1.1, by rw [Category.assoc, L.1.1.2, Category.comp_id]⟩,
    EllipticCurve.Point.asSection E σ
      ⟨σ ≫ L.1.2.1, by rw [Category.assoc, L.1.2.2, Category.comp_id]⟩),
    by sorry⟩

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

/-- **(T-H4 = Loeffler Prop 3.8.2, BOTH halves)** `P_H` is relatively representable
**and the representing objects are finite étale** over the base when `N` is invertible
(verbatim: "relatively representable and étale … finite étale") — the étale conjunct
was missing from the statement until 2026-07-06. (Proof route for `H = {1}`: the open
subscheme of `E[N] ×_S E[N]` cut by non-vanishing of Weil pairings — consumes
workstream C; for general `H`: the quotient by `H` — consumes stream Q. The two
conjuncts share one representing object; identifying them across the two ∃'s is part
of the ticket.) -/
theorem gammaHNaive_relativelyRepresentable (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R)) :
    (gammaHNaiveProblem R N H).RelativelyRepresentable ∧
      ∀ X : EllObj R, ∃ (Z : Scheme.{u}) (f : Z ⟶ X.base), IsFinite f ∧ Etale f ∧
        ∀ {T : Scheme.{u}} (g : T ⟶ X.base), Nonempty
          ({ h : T ⟶ Z // h ≫ f = g } ≃
            (gammaHNaiveProblem R N H).obj (Opposite.op (X.pullbackAlong g))) := by
  sorry

/-- **(T-H5 = Loeffler Prop 3.8.3, the rigidity criterion for arbitrary level)** Over
`R` with `6N` invertible: `P_H` is rigid iff the preimage of `H` in `SL₂(ℤ)` is
torsion-free ("contains no elements of finite order — i.e. has no elliptic points and
does not contain `−1`"). -/
theorem gammaHNaive_rigid_iff (N : ℕ) [NeZero N] [Nontrivial R]
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
    (gammaHNaiveProblem R N H).Representable ∧
      ∀ X : EllObj R, Nonempty ((gammaHNaiveProblem R N H).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) := by sorry

/-- **(T-H7, the honest stack statement at small `N`)** For `N ≤ 2` the full-level
problem is NOT rigid — `[-1]` is a nontrivial automorphism acting trivially on all
level data (on `E[2]`, `−P = P`) — so no fine scheme exists and the object of record
is the levelled groupoid (design D6). This is the precise sense in which "for full
level `N ≤ 2` we only get a stack".

Hypotheses per the adversarial pass (2026-07-05, DEF-1): `N` invertible (over an
`𝔽₂`-algebra naive full level-2 structures do not exist — `E[2]` is infinitesimal —
so the problem is vacuously rigid), and an object with nonempty base (empty-base
objects witness nothing). Proof route: pass to the full-level trivialisation scheme
of any `X` (finite étale surjective, so nonempty base persists), where the
tautological level point is fixed by `[-1] ≠ 𝟙`. -/
theorem gammaFullNaive_not_rigid_of_le_two (N : ℕ) [NeZero N] (hN : N ≤ 2)
    (hinv : IsUnit ((N : ℕ) : R)) (hR : ∃ X : EllObj R, Nonempty X.base) :
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

/-- **(T-H8 = GME Thm 2.6.8 scope; over-ℤ refinements = KM 4.7.2/5.1, ⧗KM)** For
`N ≥ 3` with `N` **invertible**, the Drinfeld full-level problem is rigid and
representable.

ADVERSARIAL FIX (2026-07-06): the previous arbitrary-ring form was FALSE — in char
`p ∣ N` with `N = p^k` (e.g. `N = 3`, supersingular `E/F̄₃`), the pair `(0, 0)` IS a
Drinfeld Γ(N)-structure (`Σ_{a,b} [a·0 + b·0] = N²[0] = E[N]` as divisors, and
`Norm(f) = f(0)^{N²} = ∏ f(0)` on the local ring `k[t]/(t^{N²})` — independently
verified), and `[-1] ≠ 𝟙` fixes it, so the problem is not rigid, hence (Yoneda +
cartesian-square rigidity) not representable. The over-ℤ statement has genuine fine
print — GME's in-hand over-ℤ Aut-triviality needs coprime `m, n ≥ 3` dividing `N`
(decomposition-gme2 B9/Y.6) — and is ⧗KM: cut it verbatim from the full text, never
from memory. (KM refinements for phase 2: `Y(N)` affine, flat finite over the
`j`-line, regular.) -/
theorem gammaFullDrinfeld_representable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) :
    (gammaFullDrinfeldProblem R N).Rigid ∧
      (gammaFullDrinfeldProblem R N).Representable := by sorry

/-- **(T-H9, `Γ₁` analogue — over-ℤ refinement is KM 5.x, ⧗KM)** For `N ≥ 4` with `N`
**invertible**, the Drinfeld `Γ₁(N)` problem is rigid and representable.

ADVERSARIAL FIX (2026-07-06): over an arbitrary ring this was FALSE, refuted by a
source already in hand — KM Caution 1.4.3: over `F̄_p` the zero section has exact
order `pⁿ` for every `n` (it generates `Ker Fⁿ`), so for `N = p^k ≥ 4` in char `p`
the zero section is a Drinfeld Γ₁(N)-structure fixed by `[-1] ≠ 𝟙`: not rigid, not
representable. "`Y₁(N)` over `ℤ`" awaits the verbatim KM statement. -/
theorem gammaOneDrinfeld_representable (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    (gammaOneDrinfeldProblem R N).Rigid ∧
      (gammaOneDrinfeldProblem R N).Representable := by sorry

end DrinfeldOverZ

namespace EllipticCurve

/-- The **levelled category**: elliptic curves over `S` with (naive) full level-`N`
structure; morphisms are pointed `S`-morphisms carrying one level structure to the
other. Its **core** is the levelled groupoid — the value at `S` of the moduli
**stack** of full level-`N` structures; as with `HomOver`, non-invertible levelled
endomorphisms exist (`[1+N]`), so the category itself is not a groupoid (adversarial
pass 2026-07-06). For `N ≥ 3` (invertible) the *automorphisms* are trivial
(`aut_trivial_of_fullLevel`); for `N ≤ 2` the levelled groupoid is the object of
record (`gammaFullNaive_not_rigid_of_le_two`). -/
@[ext]
structure LevelledHom {N : ℕ} [NeZero N]
    (X Y : Σ E : EllipticCurve S, E.FullLevelPt N) where
  hom : X.1 ⟶ Y.1
  level_w₁ : X.2.1.1.1 ≫ hom.hom = Y.2.1.1.1
  level_w₂ : X.2.1.2.1 ≫ hom.hom = Y.2.1.2.1

noncomputable instance levelledCategory (N : ℕ) [NeZero N] :
    Category (Σ E : EllipticCurve S, E.FullLevelPt N) where
  Hom := LevelledHom
  id X := ⟨𝟙 X.1, by sorry, by sorry⟩
  comp f g := ⟨f.hom ≫ g.hom, by sorry, by sorry⟩
  id_comp := by intros; sorry
  comp_id := by intros; sorry
  assoc := by intros; sorry

end EllipticCurve

end ModularCurves
