import ModularCurves.WeilPairing.Basic
import ModularCurves.Moduli.Representability
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The twisted modular curve Y(ρ̄_N) (Buzzard, *Formalizing Fermat* Lecture 8, p. 33)

The post-1980s target. Verbatim from the source slides:

> "We have `ρ̄_N : Gal(ℚ̄/ℚ) → Aut_{ℤ/Nℤ}(V)` equipped with an alternating
> `Gal(ℚ̄/ℚ)`-equivariant perfect pairing to `μ_N(ℚ̄)`. […] Now we can look at the functor
> on ℚ-schemes `S` parametrising elliptic curves `E/S` such that `E[N] ≅ ρ̄_N` as
> representations-with-pairing. This functor is representable by a smooth, geometrically
> irreducible curve `Y(ρ̄_N)` over ℚ. NB irreducibility is proved complex-analytically by
> uniformising the ℂ-points of the curve by the upper half plane."

Prerequisite (registered DS5): the dictionary between continuous `Gal(ℚ̄/ℚ)`-modules on
finite abelian groups and finite étale group schemes over `ℚ` (Grothendieck–Galois). The
scheme `V_ρ` attached to `ρ` is registered data with its characterising properties stated;
construction ticket chain `T-F1*` (Galois descent of the constant group scheme —
"a scary lemma (étale descent of morphisms)", Loeffler §3.6).

Statement policy: the *field-points* description (what Buzzard's application consumes:
`K`-points for `K` of characteristic zero "canonically" biject with pairs
`(E/K, E[N] ≅ ρ carrying the Weil pairing to p)`) is stated in full, with the canonicity
made precise as naturality in `K`; the full functor-on-`Sch/ℚ` representability is
`yRho_representable`. Geometric irreducibility is a black box (BB-IRR: 1980s,
complex-analytic uniformisation).
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

/-- The absolute Galois group of `ℚ` (with its Krull topology, from mathlib): stated as
the automorphism group of the algebraic closure, definitionally
`Field.absoluteGaloisGroup ℚ` (kept as an `abbrev` of the unfolded form so the group and
Krull-topology instances apply). -/
abbrev GalQ : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- **(T-F0)** `ℚ̄` contains exactly `N` `N`-th roots of unity (char. 0, algebraically
closed). Input hypothesis for mathlib's `modularCyclotomicCharacter`. -/
theorem card_rootsOfUnity_algClosureQ (N : ℕ) [NeZero N] :
    Fintype.card { x // x ∈ rootsOfUnity N (AlgebraicClosure ℚ) } = N := by sorry

/-- A mod-`N` Galois representation datum for the twisted modular curve: a continuous
action of `Gal(ℚ̄/ℚ)` on `(ℤ/N)²` with cyclotomic determinant, together with the pairing
normalisation `p`. Buzzard p. 33: `ρ̄_N` "equipped with an alternating Gal-equivariant
perfect pairing to `μ_N(ℚ̄)`" — the pairing datum is an equivariant identification of
`Λ²(ρ) = det ρ` with `μ_N(ℚ̄)`, unique up to `(ℤ/N)ˣ`. -/
structure GaloisRepData (N : ℕ) [NeZero N] where
  /-- The representation. -/
  ρ : GalQ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod N)
  /-- Continuity: the kernel is open (equivalently, the action factors through a finite
  quotient — `ZMod N` is discrete). -/
  ker_open : IsOpen (X := GalQ) (MonoidHom.ker ρ : Set GalQ)
  /-- Cyclotomic determinant: `det ∘ ρ` is the mod-`N` cyclotomic character of `ℚ`. -/
  det_cyclo : ∀ σ : GalQ,
    Matrix.GeneralLinearGroup.det (ρ σ) =
      modularCyclotomicCharacter (AlgebraicClosure ℚ) (card_rootsOfUnity_algClosureQ N) σ.toRingEquiv
  /-- The pairing normalisation `p`: a group isomorphism from `ℤ/N` (the line `Λ²ρ`,
  carrying the Galois action through `det ∘ ρ`) to `μ_N(ℚ̄)`, Galois-equivariantly. -/
  p : Multiplicative (ZMod N) ≃* rootsOfUnity N (AlgebraicClosure ℚ)
  p_equivariant : ∀ (σ : GalQ) (x : Multiplicative (ZMod N)),
    σ ((p x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((p (x ^ ((modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (card_rootsOfUnity_algClosureQ N) σ.toRingEquiv : (ZMod N)ˣ) : ZMod N).val) :
          (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)

/-- **(DS5, ticket chain T-F1)** The finite étale group scheme `V_ρ` over `ℚ` attached to
the Galois module `(ℤ/N)²` via `ρ` (Grothendieck–Galois / Galois descent of the constant
group scheme `(ℤ/N)²` along the splitting field of `ρ`). DATA-SORRY (register entry DS5).
Specifications: `vRho_finite_etale`, `vRho_points` (T-F1a/b). -/
noncomputable def vRho {N : ℕ} [NeZero N] (D : GaloisRepData N) : Scheme.{0} := sorry

/-- **(DS5)** The structure morphism of `V_ρ`. -/
noncomputable def vRhoπ {N : ℕ} [NeZero N] (D : GaloisRepData N) :
    vRho D ⟶ Spec (.of ℚ) := sorry

/-- **(T-F1a, specification of DS5)** `V_ρ ⟶ Spec ℚ` is finite étale (of degree `N²`). -/
theorem vRhoπ_finite_etale {N : ℕ} [NeZero N] (D : GaloisRepData N) :
    IsFinite (vRhoπ D) ∧ Etale (vRhoπ D) := by sorry

/-- **(DS5c / T-F1b, specification of DS5)** The canonical `ℚ̄`-points description of
`V_ρ`: points over `ℚ̄` biject with `(ℤ/N)²`. Registered as canonical data (it is part of
the Grothendieck–Galois construction of DS5); the `GalQ`-equivariance of this bijection
(the action on points being `ρ`) is the companion specification `vRhoPointsEquiv_equivariant`
in ticket `T-F1b`. -/
noncomputable def vRhoPointsEquiv {N : ℕ} [NeZero N] (D : GaloisRepData N) :
    { h : Spec (.of (AlgebraicClosure ℚ)) ⟶ vRho D //
        h ≫ vRhoπ D = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) }
      ≃ (Fin 2 → ZMod N) := sorry

/-- The `(ℤ/N)²`-coordinate of a `ℚ̄`-valued raw `N`-torsion point of `E`, read through a
`ρ`-level isomorphism and the canonical points description of `V_ρ`. Real construction
(pullback plumbing) modulo the registered data it consumes. -/
noncomputable def coord {N : ℕ} [NeZero N] (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) {E : EllipticCurve T}
    (torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x : E.Point t) (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero) : Fin 2 → ZMod N :=
  vRhoPointsEquiv D
    ⟨E.pointToTorsion x hx ≫ torsionIso.hom ≫ pullback.fst _ _, by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc,
        ← Category.assoc]
      sorry⟩

/-- The pairing-compatibility relation at a geometric point: `e_N(x,y) = p(a₁b₂ − a₂b₁)`
where `(a₁,a₂), (b₁,b₂)` are the coordinates of `x, y`. The two sides live in
`Γ(Spec ℚ̄, ⊤)ˣ`-roots and `μ_N(ℚ̄)` respectively and are compared through the canonical
`Γ`–`Spec` ring isomorphism; the definitional unfolding is ticket `T-F3` (this `Prop` is
`sorry`-defined *as a definition of the relation*, discharged by T-F3 — register DS5d). -/
def PairingCompatAt {N : ℕ} [NeZero N] (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) {E : EllipticCurve T}
    (torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) : Prop := sorry

/-- A **ρ-level structure** on an elliptic curve `E` over a `ℚ`-scheme `T`: an
isomorphism of group schemes over `T` between `E[N]` and the pullback of `V_ρ`, carrying
the Weil pairing `e_N` to the pairing `p` of the datum.

Skeleton form: the underlying scheme isomorphism over `T`, with group-compatibility and
pairing-compatibility recorded as `Prop` fields against the registered structures. The
pairing condition is stated on geometric points via `weilPairingEval`; strengthening to
the scheme-level identity is ticket `T-F3`. -/
structure RhoLevelStructure {N : ℕ} [NeZero N] (D : GaloisRepData N)
    {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℚ)) (E : EllipticCurve T) where
  /-- The isomorphism `E[N] ≅ V_ρ ×_ℚ T` of `T`-schemes. -/
  torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT
  over_T : torsionIso.hom ≫ pullback.snd _ _ = E.torsionπ N
  /-- Compatibility of the identification with the `(ℤ/N)²`-coordinates on geometric
  points: composing a `ℚ̄`-valued torsion point of `E` with the isomorphism and reading
  off coordinates via `vRhoPointsEquiv` is *additive* and carries the Weil pairing to the
  standard symplectic pairing transported through `p`. Stated on geometric points valued
  in `ℚ̄`; the scheme-level (group-object morphism) form is ticket `T-F3`. -/
  coords_additive : ∀ (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hxy : (x + y).1 ≫ E.mulByHom N = t ≫ E.zero),
    coord D sT torsionIso t ht (x + y) hxy =
      coord D sT torsionIso t ht x hx + coord D sT torsionIso t ht y hy
  /-- Pairing compatibility: the Weil pairing of two `ℚ̄`-valued torsion points equals
  `p` of the standard symplectic pairing `a₁b₂ − a₂b₁` of their coordinates.
  (`Γ(Spec ℚ̄, ⊤)`-valued roots of unity are compared with `μ_N(ℚ̄)` through the
  canonical `Γ`–`Spec` isomorphism; equation recorded through `pairingCompatStatement`
  to keep the field readable.) -/
  pairing_compat : ∀ (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero),
    PairingCompatAt D sT torsionIso t ht x y hx hy

/-- **(T-F4 = Buzzard p. 33, the main statement)** The twisted modular curve exists:
there is a scheme `Y = Y(ρ̄_N)` over `ℚ`, smooth of relative dimension 1 and affine, such
that for every `ℚ`-scheme `T` the `T`-points of `Y` over `ℚ` biject with isomorphism
classes of pairs `(E/T, α : ρ-level structure)`, naturally in `T`. Requires `N ≥ 3` (the
underlying `[Γ(N)]` must be rigid — Loeffler Prop 3.8.3).

Geometric irreducibility of `Y` is stated separately (`yRho_geometricallyIrreducible`,
black box BB-IRR: "proved complex-analytically by uniformising the ℂ-points … by the
upper half plane" — sorry-able 1980s input). -/
theorem yRho_representable {N : ℕ} [NeZero N] (hN : 3 ≤ N) (D : GaloisRepData N) :
    ∃ (Y : Scheme.{0}) (sY : Y ⟶ Spec (.of ℚ)),
      SmoothOfRelativeDimension 1 sY ∧ IsAffineHom sY ∧
      ∀ (T : Scheme.{0}) (sT : T ⟶ Spec (.of ℚ)),
        Nonempty ({ h : T ⟶ Y // h ≫ sY = sT } ≃
          Quot (fun (a b : Σ E : EllipticCurve T, RhoLevelStructure D sT E) =>
            Nonempty (a.1.E ≅ b.1.E))) := by sorry

/-- **(T-F5, BB-IRR)** `Y(ρ̄_N)` is geometrically irreducible over `ℚ`. Black box:
complex-analytic uniformisation of the ℂ-points by the upper half-plane (Buzzard p. 33;
"Proof: See 1980s"). Stated as: the base change to `ℚ̄` is irreducible. -/
theorem yRho_geometricallyIrreducible {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (D : GaloisRepData N) (Y : Scheme.{0}) (sY : Y ⟶ Spec (.of ℚ))
    (hY : SmoothOfRelativeDimension 1 sY) :
    IrreducibleSpace ↥(pullback sY
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) := by sorry

end ModularCurves
