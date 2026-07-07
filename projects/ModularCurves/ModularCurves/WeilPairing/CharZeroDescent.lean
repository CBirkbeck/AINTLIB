import ModularCurves.WeilPairing.Basic
import ModularCurves.Moduli.Stack

/-!
# The `T`-relative Weil pairing by fppf descent (T-C0e, `weilPairingCharZero`)

The DS4 Weil pairing of record (`WeilPairing/Basic.lean`, `EllipticCurve.weilPairing`) is the
`S`-morphism `e_N : E[N] ×_S E[N] ⟶ μ_{N,S}`, registered there as a DATA-SORRY. Per the v9
expert review (2026-07-07, §"Weil pairing"), the pairing the moduli functor `Y(ρ̄)` needs is
exactly this `T`-relative morphism over arbitrary `Spec ℚ`-schemes — **not** the field-valued
descent `exists_pairingAlgebraHom_of_galoisEquivariant` of `WeilPairing/EtaleDescent.lean`,
which is only the geometric-fibre (field-base) pairing.

This file supplies the **char-0 construction** of that morphism by the route the review named:
*build the pairing étale-locally on `S` — where the finite-étale `E[N]` trivialises — then
descend it.* The descent half is gate-free and general; the input it consumes is a local pairing
on a trivialising fppf cover together with its gluing (cocycle) datum. Concretely:

* `weilPairingCharZero E N p ζ' hcocyc` descends a morphism `ζ'` — defined on the base change of
  `E[N] ×_S E[N]` along an fppf cover `p : S' ⟶ S` and valued in the fixed target `μ_{N,S}` — to
  a morphism `E[N] ×_S E[N] ⟶ μ_{N,S}` over `S`, using `descend_hom_of_effectiveEpi`
  (`Moduli/Stack.lean`; fppf covers are effective epimorphisms by subcanonicity of the fppf
  topology). The base change of the cover along the structure map `E[N] ×_S E[N] ⟶ S` is again
  fppf (`Flat`/`LocallyOfFinitePresentation`/`Surjective` are stable under base change), so the
  mathlib `EffectiveEpi` instance fires.

**Labelled inputs (the gated content, isolated as hypotheses).** The cover `p` exists because
`E[N]` is finite étale when `N` is invertible (`torsionπ_etale`, which rests on the T-B5 box
`mulByHom_formallyUnramified`); the local pairing `ζ'` and its cocycle `hcocyc` come from
trivialising `E[N]` (and `μ_N`) on `p` and putting the standard symplectic determinant pairing
there. Constructing those data from the trivialisation is the T-W7-scale step (the point-level
`E[N] ≅ (ℤ/N)²` identification funnels into the group-law/atlas refactor); here they are the
theorem's hypotheses, so the descent — the reviewer's "then descend" half — is discharged
**gate-free**. Supplying `(p, ζ', hcocyc)` from an étale-local full-level trivialisation is what
would discharge the DS4 `weilPairing` sorry over `ℚ`-schemes.

Source: KM 2.8; the descent is SGA 1 VIII / Stacks 023Q (fppf covers are effective epis).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- The structure morphism `E[N] ×_S E[N] ⟶ S` of the Weil-pairing source. -/
noncomputable def torsionSqπ (N : ℕ) : pullback (E.torsionπ N) (E.torsionπ N) ⟶ S :=
  pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionπ N

/-- **(T-C0e)** The char-0 Weil pairing `E[N] ×_S E[N] ⟶ μ_{N,S}`, constructed by fppf descent
of a local pairing `ζ'` given on the base change of `E[N] ×_S E[N]` along a trivialising fppf
cover `p : S' ⟶ S`. The pulled-back cover `pullback.fst (E.torsionSqπ N) p` is fppf (base change
of `p`), hence an effective epimorphism, so a morphism into the fixed target `μ_{N,S}` that
coequalises its kernel pair (`hcocyc`) descends uniquely. See the module docstring for the
labelled-input convention. -/
noncomputable def weilPairingCharZero (N : ℕ) [NeZero N]
    {S' : Scheme.{u}} (p : S' ⟶ S)
    [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (ζ' : pullback (E.torsionSqπ N) p ⟶ muN S N)
    (hcocyc : pullback.fst (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ'
        = pullback.snd (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ') :
    pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N :=
  haveI : Surjective (pullback.fst (E.torsionSqπ N) p) :=
    MorphismProperty.pullback_fst _ _ ‹Surjective p›
  haveI : LocallyOfFinitePresentation (pullback.fst (E.torsionSqπ N) p) :=
    MorphismProperty.pullback_fst _ _ ‹LocallyOfFinitePresentation p›
  (descend_hom_of_effectiveEpi (pullback.fst (E.torsionSqπ N) p) ζ' hcocyc).choose

/-- **(T-C0e spec, restriction)** The char-0 Weil pairing restricts along the trivialising cover
to the local pairing `ζ'` it was descended from. -/
theorem weilPairingCharZero_restrict (N : ℕ) [NeZero N]
    {S' : Scheme.{u}} (p : S' ⟶ S)
    [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (ζ' : pullback (E.torsionSqπ N) p ⟶ muN S N)
    (hcocyc : pullback.fst (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ'
        = pullback.snd (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ') :
    pullback.fst (E.torsionSqπ N) p ≫ E.weilPairingCharZero N p ζ' hcocyc = ζ' :=
  haveI : Surjective (pullback.fst (E.torsionSqπ N) p) :=
    MorphismProperty.pullback_fst _ _ ‹Surjective p›
  haveI : LocallyOfFinitePresentation (pullback.fst (E.torsionSqπ N) p) :=
    MorphismProperty.pullback_fst _ _ ‹LocallyOfFinitePresentation p›
  (descend_hom_of_effectiveEpi (pullback.fst (E.torsionSqπ N) p) ζ' hcocyc).choose_spec.1

/-- **(T-C0e spec, over `S` — cf. `weilPairing_over`)** If the local pairing `ζ'` is a morphism
over `S` (lands in `μ_{N,S}` compatibly with the structure map), then so is the descended pairing:
`e_N` followed by `μ_{N,S} ⟶ S` is the projection `E[N] ×_S E[N] ⟶ S`. -/
theorem weilPairingCharZero_over (N : ℕ) [NeZero N]
    {S' : Scheme.{u}} (p : S' ⟶ S)
    [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (ζ' : pullback (E.torsionSqπ N) p ⟶ muN S N)
    (hcocyc : pullback.fst (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ'
        = pullback.snd (pullback.fst (E.torsionSqπ N) p) (pullback.fst (E.torsionSqπ N) p) ≫ ζ')
    (hover : ζ' ≫ muNπ S N = pullback.fst (E.torsionSqπ N) p ≫ E.torsionSqπ N) :
    E.weilPairingCharZero N p ζ' hcocyc ≫ muNπ S N = E.torsionSqπ N := by
  haveI : Surjective (pullback.fst (E.torsionSqπ N) p) :=
    MorphismProperty.pullback_fst _ _ ‹Surjective p›
  haveI : LocallyOfFinitePresentation (pullback.fst (E.torsionSqπ N) p) :=
    MorphismProperty.pullback_fst _ _ ‹LocallyOfFinitePresentation p›
  haveI : Epi (pullback.fst (E.torsionSqπ N) p) := inferInstance
  refine (cancel_epi (pullback.fst (E.torsionSqπ N) p)).mp ?_
  rw [← Category.assoc, E.weilPairingCharZero_restrict N p ζ' hcocyc, hover]

end EllipticCurve

end ModularCurves
