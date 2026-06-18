import HasseWeil.Endomorphism

/-!
# The Dual Isogeny: the `IsDualOf` relation and its witness-parametric API

Following Silverman III.6, this file defines the dual-isogeny *relation*
`IsDualOf` for the Basic-world `Isogeny`, together with its witness-parametric
API: every theorem takes a concrete dual (or the defining composition
identities) as an explicit hypothesis.

## The universal `exists_dual` was REFUTED (B2)

This file formerly closed with the keystone sorry

> `exists_dual (α : Isogeny E E) : ∃! β : Isogeny E E, IsDualOf E β α`

That statement is **false** for the Basic-world `Isogeny` structure, two
independent ways, so it was deleted together with its `Classical.choice`
cascade (`isogDual`, `isogDual_spec`, `isogDual_comp_self`,
`self_comp_isogDual`, `isogDual_unique`, `degree_isogDual`,
`isogDual_isogDual`, `isogDual_add_of_sum_dual`, `isogDual_mulByInt_of_comp`,
`isogTrace_eq_dual`, `isogDual_comp_self_apply`):

* **Existence fails** at `α := mulByInt E 0`: the documented junk pullback
  branch (`AlgHom.id`) gives `α.degree = 1`, so the second `IsDualOf`
  conjunct contains the point-map identity `(0 : ℤ) • β P = (1 : ℤ) • P`,
  i.e. `0 = P` — false on any curve with a nonzero rational point.
  Formalized: `EC.not_exists_dual_universal`
  (`HasseWeil/EC/IsogenyAG/DualUniversal.lean`).
* **Uniqueness fails** even for genuine `α` over non-algebraically-closed
  fields: `Isogeny` carries `pullback` and `toAddMonoidHom` as *independent*
  fields, and the `IsDualOf` equations cannot pin the point-map component on
  a finite rational-point group (e.g. `[2]` on `E(𝔽₃) ≅ (ℤ/2)²` admits 15
  alternative point maps). Only pullback-level uniqueness survives:
  `IsDualOf.pullback_unique` below.

See `.mathlib-quality/b2_log.jsonl`, ticket `DUAL-LEGACY-B2`. The **true**
Silverman III.6.1 (witness-gated `∃!` with both compositions) lives in the
AG world: `HasseWeil/EC/IsogenyAG/CanonicalDual.lean`.

## What this file provides

* `IsDualOf` — the dual-isogeny relation, the hypothesis language used across
  the Hasse-bound development (`GapSpines`, `WallA/VSideDual`,
  `DegreeQuadraticForm`, `Verschiebung/IsDual`, …).
* `∃!`-packaging lemmas (`exists_dual_of_construction`,
  `exists_dual_of_constructor`, `exists_dual_iff_constructor`) for classes of
  isogenies where a constructor-plus-uniqueness pair *is* available.
* Witness-parametric III.6.2 lemmas (`isogDual_comp_self_of_witness`,
  `self_comp_isogDual_of_witness`, `degree_dual_of_witness`,
  `dual_add_of_trace_witnesses`, `dual_add_of_sum_witnesses`).
* `IsDualOf.pullback_unique` — the surviving uniqueness, at the pullback
  level.

The scalar self-duality `IsDualOf E [n] [n]` (`n ≠ 0`) is
`EC.mulByInt_isDualOf_self` in `HasseWeil/EC/IsogenyAG/DualUniversal.lean`:
its proof needs `mulByInt_comp_eq_mul` (`EC/GenericPointZsmul.lean`,
T-III-4-020b, proven), which is not in this file's import closure.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.6.1-2.
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### The dual-isogeny relation (Silverman III.6.1) -/

section DualIsogeny

variable (E : Affine F) [E.IsElliptic]

/-- The dual-isogeny relation: `β` is a (left and right) dual of `α`. -/
def IsDualOf (β α : Isogeny E E) : Prop :=
  β.comp α = mulByInt E α.degree ∧ α.comp β = mulByInt E α.degree

/-! #### Parametric forms of dual existence

The universal `∃! β, IsDualOf E β α` is **false** for the Basic-world
`Isogeny` (see the module docstring), so dual existence is always consumed in
*witness-parametric* form. For classes of isogenies where a
constructor-plus-uniqueness pair *is* available, the lemmas below package it
into the `∃!` statement. The genuine witness producers live in the AG world
(`EC/IsogenyAG/CanonicalDual.lean` and the `HasDualWitness` cascade). -/

/-- **Parametric `∃!` packaging**: given a dual for `α` and a uniqueness
    witness, conclude `∃!`. -/
theorem exists_dual_of_construction
    (α : Isogeny E E)
    (dual : Isogeny E E)
    (h_dual : IsDualOf E dual α)
    (h_unique : ∀ β, IsDualOf E β α → β = dual) :
    ∃! β : Isogeny E E, IsDualOf E β α :=
  ⟨dual, h_dual, h_unique⟩

/-- **Constructor form**: if a class-wide dual constructor and uniqueness
    witness are available, the `∃!` drops out for every `α` at once. -/
theorem exists_dual_of_constructor
    (dualOf : Isogeny E E → Isogeny E E)
    (h_dual : ∀ α, IsDualOf E (dualOf α) α)
    (h_unique : ∀ α β, IsDualOf E β α → β = dualOf α)
    (α : Isogeny E E) :
    ∃! β : Isogeny E E, IsDualOf E β α :=
  exists_dual_of_construction E α (dualOf α) (h_dual α) (h_unique α)

/-- **Characterisation of dual existence**: the universal `∃!` statement
    holds iff a constructor-plus-uniqueness pair exists. A pure
    meta-identity. (For the Basic-world `Isogeny` both sides are *false*
    universally — see `EC.not_exists_dual_universal` — but the equivalence
    remains the correct packaging on any subclass where a constructor is
    available.) -/
theorem exists_dual_iff_constructor :
    (∀ α : Isogeny E E, ∃! β : Isogeny E E, IsDualOf E β α) ↔
      ∃ dualOf : Isogeny E E → Isogeny E E,
        (∀ α, IsDualOf E (dualOf α) α) ∧
        (∀ α β, IsDualOf E β α → β = dualOf α) := by
  refine ⟨fun h ↦ ⟨fun α ↦ (h α).choose, fun α ↦ (h α).choose_spec.1,
           fun α β hβ ↦ (h α).choose_spec.2 β hβ⟩, ?_⟩
  rintro ⟨dualOf, h_dual, h_unique⟩ α
  exact exists_dual_of_constructor E dualOf h_dual h_unique α

/-! #### Witness-parametric dual properties

Each theorem below takes a dual as an explicit argument and derives the
defining properties unconditionally; the III.6.2(a/b/c) and III.8 consumers
downstream are stated on this witness-parametric path. -/

/-- Witness-parametric form of `α̂ ∘ α = [deg α]`: the first conjunct of
    `IsDualOf`, extracted. -/
theorem isogDual_comp_self_of_witness
    (α dual : Isogeny E E) (h_dual : IsDualOf E dual α) :
    dual.comp α = mulByInt E α.degree :=
  h_dual.1

theorem self_comp_isogDual_of_witness
    (α dual : Isogeny E E) (h_dual : IsDualOf E dual α) :
    α.comp dual = mulByInt E α.degree :=
  h_dual.2

/-- Witness-parametric **Silverman III.6.2(a)**: a witness dual of `α` has
    degree equal to `α.degree` (for nonzero `α`). -/
theorem degree_dual_of_witness
    (α dual : Isogeny E E) (hα : 0 < α.degree)
    (h_dual : IsDualOf E dual α) :
    dual.degree = α.degree := by
  have h : dual.comp α = mulByInt E α.degree := h_dual.1
  have hα_ne : (α.degree : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hα.ne'
  have hdeg := Isogeny.comp_degree dual α
  rw [h, mulByInt_degree E (α.degree : ℤ) hα_ne] at hdeg
  have hpow : ((α.degree : ℤ) ^ 2).toNat = α.degree ^ 2 := by
    have : (α.degree : ℤ) ^ 2 = (α.degree ^ 2 : ℕ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [hpow, sq] at hdeg
  exact Nat.eq_of_mul_eq_mul_left hα hdeg.symm

variable {E}

/-- **The surviving uniqueness: duals of `α` agree at the pullback level.**

    The full `∃!` uniqueness is false (the point-map component of `Isogeny`
    is an independent field which the `IsDualOf` equations cannot pin down
    over non-algebraically-closed fields), but the function-field component
    *is* unique: from `β ∘ α = [deg α] = β' ∘ α` and injectivity of `α*`
    (an `F`-algebra hom of fields), the pullbacks of `β` and `β'` agree. -/
theorem IsDualOf.pullback_unique {α β β' : Isogeny E E}
    (h : IsDualOf E β α) (h' : IsDualOf E β' α) :
    β.pullback = β'.pullback := by
  have hcomp : β.comp α = β'.comp α := h.1.trans h'.1.symm
  refine AlgHom.ext fun z ↦ ?_
  exact α.pullback_injective
    (congrArg (fun γ : Isogeny E E ↦ γ.pullback z) hcomp)

end DualIsogeny

/-! ### Dual additivity (Silverman III.6.2c) -/

section DualAdditivity

variable (E : Affine F) [E.IsElliptic]

/-- **Silverman III.6.2(c) — witness-parametric form**.

    Given witness duals `α_dual`, `β_dual`, `αβ_dual` for `α`, `β`,
    `αβ = α + β`, each satisfying its trace identity at the `AddMonoidHom`
    level (with integer traces `tα`, `tβ`, `tαβ`), and integer trace
    additivity `tαβ = tα + tβ`, conclude

      `αβ_dual.toAddMonoidHom = α_dual.toAddMonoidHom + β_dual.toAddMonoidHom`.

    This is the core mathematical content of III.6.2(c) as a pure algebraic
    identity, stated entirely on explicit witnesses (the choice-based
    `isogDual` is gone — its underlying `exists_dual` was refuted).
    Combines with trace additivity (from III.6.3 QF + III.8) to give
    Silverman III.6.2(c) in the witness-parametric style used across
    `DegreeQuadraticForm.lean`. -/
theorem dual_add_of_trace_witnesses
    (α β αβ α_dual β_dual αβ_dual : Isogeny E E)
    (tα tβ tαβ : ℤ)
    (hαβ_hom : αβ.toAddMonoidHom = α.toAddMonoidHom + β.toAddMonoidHom)
    (hα_trace : α.toAddMonoidHom + α_dual.toAddMonoidHom =
      (mulByInt E tα).toAddMonoidHom)
    (hβ_trace : β.toAddMonoidHom + β_dual.toAddMonoidHom =
      (mulByInt E tβ).toAddMonoidHom)
    (hαβ_trace : αβ.toAddMonoidHom + αβ_dual.toAddMonoidHom =
      (mulByInt E tαβ).toAddMonoidHom)
    (h_tr_add : tαβ = tα + tβ) :
    αβ_dual.toAddMonoidHom =
      α_dual.toAddMonoidHom + β_dual.toAddMonoidHom := by
  ext P
  have hα_P := congr_fun (congr_arg DFunLike.coe hα_trace) P
  have hβ_P := congr_fun (congr_arg DFunLike.coe hβ_trace) P
  have hαβ_P := congr_fun (congr_arg DFunLike.coe hαβ_trace) P
  have hhom_P := congr_fun (congr_arg DFunLike.coe hαβ_hom) P
  simp only [AddMonoidHom.add_apply] at hα_P hβ_P hαβ_P hhom_P
  rw [show (mulByInt E tα).toAddMonoidHom P = tα • P from rfl] at hα_P
  rw [show (mulByInt E tβ).toAddMonoidHom P = tβ • P from rfl] at hβ_P
  rw [show (mulByInt E tαβ).toAddMonoidHom P = tαβ • P from rfl] at hαβ_P
  have h_αd : α_dual.toAddMonoidHom P =
      tα • P - α.toAddMonoidHom P := by rw [← hα_P]; abel
  have h_βd : β_dual.toAddMonoidHom P =
      tβ • P - β.toAddMonoidHom P := by rw [← hβ_P]; abel
  have h_αβd : αβ_dual.toAddMonoidHom P =
      tαβ • P - αβ.toAddMonoidHom P := by rw [← hαβ_P]; abel
  show αβ_dual.toAddMonoidHom P =
    α_dual.toAddMonoidHom P + β_dual.toAddMonoidHom P
  rw [h_αβd, h_tr_add, add_zsmul, hhom_P, h_αd, h_βd]
  abel

/-- **Silverman III.6.2(c) — minimal witness form**: simpler statement of
    `dual_add_of_trace_witnesses` taking a single combined sum identity
    at the `AddMonoidHom` level, without mentioning integer traces.

    Useful when the caller already has the trace-sum witnesses bundled
    together pairwise. -/
theorem dual_add_of_sum_witnesses
    (α β αβ α_dual β_dual αβ_dual : Isogeny E E)
    (hαβ_hom : αβ.toAddMonoidHom = α.toAddMonoidHom + β.toAddMonoidHom)
    (h_sum : α.toAddMonoidHom + α_dual.toAddMonoidHom +
        (β.toAddMonoidHom + β_dual.toAddMonoidHom) =
      αβ.toAddMonoidHom + αβ_dual.toAddMonoidHom) :
    αβ_dual.toAddMonoidHom =
      α_dual.toAddMonoidHom + β_dual.toAddMonoidHom := by
  rw [hαβ_hom] at h_sum
  ext P
  have hP := congr_fun (congr_arg DFunLike.coe h_sum) P
  simp only [AddMonoidHom.add_apply] at hP
  have hP' : α.toAddMonoidHom P + β.toAddMonoidHom P +
        (α_dual.toAddMonoidHom P + β_dual.toAddMonoidHom P) =
      α.toAddMonoidHom P + β.toAddMonoidHom P +
        αβ_dual.toAddMonoidHom P := by
    rw [← hP]; abel
  exact (add_left_cancel hP').symm

end DualAdditivity

end HasseWeil
