/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-Q2 (statements; the
proofs are KM A7.1.1 = SGA III Exp. V Thm 4.1 territory and are deliberately left
as WIP `sorry`s per the ticket scope).
-/
import ModularCurves.ForMathlib.InvariantBaseChange
import Mathlib.RingTheory.Etale.Basic

/-!
# Free actions and the étale-torsor theorem (Katz–Mazur A7.1.1/A7.1.2) — statements

KM's freeness condition for a finite group `G` acting on an `R`-algebra `A`
(A7.1.1): *"G acts freely on A in the sense that for any non-zero R-algebra R', and
any element g ≠ id of G, g operates without fixed points on the set
Hom_{R-alg}(A, R')."* Under this condition:

* `IsFreeAlgebraAction` — the freeness predicate;
* `MulSemiringAction.torsorMul` — the multiplication comparison
  `A ⊗[Aᴳ] A → (G → A)`, `x ⊗ y ↦ (x·(g•y))_g`;
* `Module.Finite.of_isFreeAlgebraAction`, `Algebra.Etale.of_isFreeAlgebraAction`,
  `torsorMul_bijective_of_isFreeAlgebraAction` — KM A7.1.1: `A` is a finite étale
  `G`-torsor over `Aᴳ` (three single-conclusion statements; the torsor condition is
  the bijectivity of `torsorMul`);
* `fixedPointsBaseChange_bijective_of_isFreeAlgebraAction` — KM A7.1.2: free
  actions satisfy the base-change property `∗(A, G, R)` for every `R'`.

Proofs (`sorry`d, WIP): KM defers A7.1.1 to [SGA III, Exposé V, Thm 4.1] or
[Demazure–Gabriel, III §2, 6.1] — *"In the absence of noetherian hypotheses, this is
rather delicate."* A7.1.2 follows by faithfully flat descent along `Aᴳ → A` from the
torsor triviality; it becomes provable here once A7.1.1 lands.

The stabilizer dictionary: freeness in the above sense says exactly that no
`g ≠ 1` fixes any point of `Spec A` valued in any ring — for modular curves this is
the "no elliptic points" condition under which the level quotients stay schemes.
-/

universe u

open TensorProduct

variable (G : Type*) [Group G]
variable (R A : Type u)
variable [CommRing R] [CommRing A] [Algebra R A]
variable [MulSemiringAction G A] [SMulCommClass G R A] [SMulCommClass R G A]

/-- **KM A7.1.1's freeness condition**: `G` acts freely on the `R`-algebra `A` if for
every nonzero `R`-algebra `R'` no `g ≠ 1` fixes an `R`-algebra point
`A →ₐ[R] R'`. (Verbatim: "for any non-zero R-algebra R', and any element g ≠ id of
G, g operates without fixed points on the set Hom_{R-alg}(A, R')".) -/
def IsFreeAlgebraAction : Prop :=
  ∀ g : G, g ≠ 1 → ∀ (R' : Type u) [CommRing R'] [Algebra R R'] [Nontrivial R']
    (φ : A →ₐ[R] R'), ∃ a : A, φ (g • a) ≠ φ a

/-- **(T-Q2-A711, step 1 — the Chase–Harrison–Rosenberg bridge; PROVEN)** KM's freeness
condition implies the pointwise CHR condition: at every prime `𝔭` of `A` and every `g ≠ 1`
there is `a : A` with `g • a - a ∉ 𝔭`.

Take KM's `R' := A ⧸ 𝔭` (nonzero because `𝔭` is prime) and `φ :=` the quotient map. This is
the hypothesis under which the classical Galois theory of commutative rings
(Chase–Harrison–Rosenberg, Auslander–Goldman) proves `A ⊗_{Aᴳ} A ≅ ∏_G A` and étaleness —
i.e. the route by which `torsorMul_bijective_of_isFreeAlgebraAction` and
`Algebra.Etale.of_isFreeAlgebraAction` below will be discharged, KM's own reference being
[SGA III, Exp. V, Thm 4.1] (not in `refs/`). -/
theorem chr_of_isFreeAlgebraAction (hfree : IsFreeAlgebraAction G R A)
    (p : Ideal A) [hp : p.IsPrime] (g : G) (hg : g ≠ 1) :
    ∃ a : A, g • a - a ∉ p := by
  haveI : Nontrivial (A ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  obtain ⟨a, ha⟩ := hfree g hg (A ⧸ p) (Ideal.Quotient.mkₐ R p)
  refine ⟨a, fun hmem => ha ?_⟩
  have h0 : (Ideal.Quotient.mkₐ R p) (g • a - a) = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0

namespace MulSemiringAction

/-- The torsor-multiplication comparison map `A ⊗[Aᴳ] A → (G → A)`,
`x ⊗ y ↦ (x · (g • y))_g` (KM A7.1.1: "the natural map A ⊗_{A^G} A → ∏_{g∈G} A,
x⊗y ↦ (⋯, x⊗g(y), ⋯)"). Its bijectivity is the `G`-torsor condition for
`Aᴳ → A`. -/
noncomputable def torsorMul :
    A ⊗[FixedPoints.subalgebra R A G] A →ₐ[FixedPoints.subalgebra R A G] (G → A) :=
  Algebra.TensorProduct.lift
    (Pi.constAlgHom (FixedPoints.subalgebra R A G) G A)
    (AlgHom.pi fun g => MulSemiringAction.toAlgHom (FixedPoints.subalgebra R A G) A g)
    (fun _ _ => Commute.all _ _)

omit [SMulCommClass R G A] in
@[simp]
theorem torsorMul_tmul (x y : A) (g : G) :
    torsorMul G R A (x ⊗ₜ y) g = x * g • y := rfl

end MulSemiringAction

variable [Finite G]

/-- **KM A7.1.1, finiteness part** (statement; proof: SGA III Exp. V Thm 4.1):
for a free action, `A` is finite over the invariants. WIP `sorry` per ticket
T-Q2's statement-only scope. -/
theorem Module.Finite.of_isFreeAlgebraAction (hfree : IsFreeAlgebraAction G R A) :
    Module.Finite (FixedPoints.subalgebra R A G) A := by
  sorry

/-- **KM A7.1.1, étaleness part** (statement; proof: SGA III Exp. V Thm 4.1;
"In the absence of noetherian hypotheses, this is rather delicate"): for a free
action, `A` is étale over the invariants. WIP `sorry` per ticket T-Q2's
statement-only scope. -/
theorem Algebra.Etale.of_isFreeAlgebraAction (hfree : IsFreeAlgebraAction G R A) :
    Algebra.Etale (FixedPoints.subalgebra R A G) A := by
  sorry

/-- **KM A7.1.1, torsor part** (statement): for a free action the multiplication
comparison `A ⊗[Aᴳ] A ≅ ∏_G A` is bijective — `Spec A` is a `G`-torsor over
`Spec Aᴳ`. WIP `sorry` per ticket T-Q2's statement-only scope. -/
theorem torsorMul_bijective_of_isFreeAlgebraAction
    (hfree : IsFreeAlgebraAction G R A) :
    Function.Bijective (MulSemiringAction.torsorMul G R A) := by
  sorry

/-- **KM A7.1.2** (statement): free actions satisfy base change for rings of
invariants — `∗(A, G, R, R')` for every `R'`. (KM's proof: extend scalars of the
étale torsor and use `(A ⊗ R')^G = A^G ⊗ R'` for trivializable torsors.) WIP
`sorry`; becomes provable here once A7.1.1 lands. -/
theorem fixedPointsBaseChange_bijective_of_isFreeAlgebraAction
    (hfree : IsFreeAlgebraAction G R A)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    Function.Bijective
      (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R')) := by
  sorry
