/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.SeparableWitnesses

/-!
# The generic-point covariance leaf `hgcomm` is additive (reviewer round-21 formal-local route)

The single residual leaf for the translation covariance `hcomm'` and the separable degree match
`#ker = deg` of a genuine isogeny `φ` (over any field, in particular over `K̄`) is the
**generic-point covariance** (`MapTranslateGenericPoint`)

  `hgcomm : Point.map τ_S (g P_gen) = g P_gen + lift (φ S)`,

i.e. `φ(P_gen + S) = φ(P_gen) + φ(S)` read at the generic point for a genuine action `g`
(Silverman III.8.2, generic-point form; see `SeparableWitnesses.lean`).

This file establishes that `hgcomm` is **additive in the geometric action**: the round-21 reviewer's
structural decomposition (`φ(P+S) − φ(P) = φ(S)`, with `1 − π = "add P and −πP"` and
`rπ − s = r·πP + (−s)·P`) reduces `hgcomm` for a genuine *sum* isogeny `addIsog α₁ α₂` to `hgcomm`
for the two components.  Concretely (`mapTranslateGenericPoint_add`): if `g₁`, `g₂` satisfy the
generic-point covariance against `α₁`, `α₂`, then `g₁ + g₂` satisfies it against any isogeny `φ`
whose point map is `α₁.toAddMonoidHom + α₂.toAddMonoidHom` (e.g. `addIsog α₁ α₂`, whose
`toAddMonoidHom` is literally that sum).  The proof is pure additive bookkeeping:

* `Point.map τ_S` is an `AddMonoidHom` (`Affine.Point.map_add`), so it distributes over
  `(g₁ + g₂) P_gen = g₁ P_gen + g₂ P_gen`;
* each summand is rewritten by the component `hgcomm`;
* `liftPointToKE` is an `AddMonoidHom` (`liftPointToKE_add`), so the two lifts recombine to
  `lift (α₁ S + α₂ S) = lift (φ S)`.

We also supply the bridge `mapTranslateGenericPoint_canonical_of_genuine`: the leaf for the
**canonical** action `g = Point.map φ.pullback` (the form the `SeparableWitnesses` reductions
consume) follows from the leaf for *any* genuine action `g`, because `MapTranslateGenericPoint`
only constrains the value at the single point `P_gen`, and `g P_gen = Point.map φ.pullback P_gen`
for a genuine `g` (`map_pullback_genericPoint_of_isGenuineWith`).

Combined, these reduce the canonical `hgcomm` for `1 − π = addIsog(id, −π)` and
`rπ − s = addIsog(r·π, −s·id)` to the **component** generic-point covariances — for `[m]`
(`mulByInt`, free via `map_zsmul` of the master translation lemma) and for the (negated) Frobenius
`π` — exactly the structural reduction the round-21 reviewer prescribed.  The base cases for `[m]`
and `id`/`zsmul` are shipped here; the Frobenius base case is the genuine geometric content of
`hgcomm` (the relative `q`-Frobenius is not a base-field-linear map), isolated as the single
remaining leaf.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.5.2 (the differential additivity that the
  formal linear coefficient lives in), III.8.2 (translation covariance).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

section Additive

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- **The generic-point covariance leaf is additive in the geometric action** (reviewer round-21
structural decomposition of `hgcomm`; Silverman III.8.2).  If `g₁` satisfies the generic-point
covariance against `α₁` and `g₂` against `α₂`, then `g₁ + g₂` satisfies it against any isogeny `φ`
whose point map is the sum `α₁.toAddMonoidHom + α₂.toAddMonoidHom`.

This is `φ(P_gen + S) = φ(P_gen) + φ(S)` decomposed as
`(α₁ + α₂)(P_gen + S) = α₁(P_gen + S) + α₂(P_gen + S)`, read at the generic point.  Pure additive
bookkeeping: `Point.map τ_S` and `liftPointToKE` are both `AddMonoidHom`s, so they distribute over
the sums; the two component covariances rewrite each summand; the two lifts recombine via
`α₁ S + α₂ S = φ S` (`hφhom`).

For `φ = addIsog hxy hinj` the hypothesis `hφhom` is `addIsog_toAddMonoidHom` (`rfl`); so this
discharges `hgcomm` for `1 − π = addIsog(id, −π)` and `rπ − s = addIsog(r·π, −s·id)` from the two
component leaves (`[m]` free, Frobenius the genuine residual). -/
theorem mapTranslateGenericPoint_add
    (φ α₁ α₂ : Isogeny W.toAffine W.toAffine)
    (g₁ g₂ : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point)
    (hφhom : φ.toAddMonoidHom = α₁.toAddMonoidHom + α₂.toAddMonoidHom)
    (h₁ : MapTranslateGenericPoint W α₁ g₁)
    (h₂ : MapTranslateGenericPoint W α₂ g₂) :
    MapTranslateGenericPoint W φ (g₁ + g₂) := by
  intro S
  set τ := WeierstrassCurve.Affine.Point.map (W' := W) (translateAlgEquivOfPoint W S).toAlgHom
    with hτ
  -- LHS: `Point.map τ_S ((g₁ + g₂) P_gen) = Point.map τ_S (g₁ P_gen) + Point.map τ_S (g₂ P_gen)`.
  rw [AddMonoidHom.add_apply]
  have hdist : τ (g₁ (genericPoint W) + g₂ (genericPoint W)) =
      τ (g₁ (genericPoint W)) + τ (g₂ (genericPoint W)) :=
    map_add τ (g₁ (genericPoint W)) (g₂ (genericPoint W))
  rw [hdist]
  -- Rewrite each summand by the component covariance (`τ` is `set` to `Point.map τ_S`, so the
  -- component leaves `h₁ S`/`h₂ S` already mention it).
  rw [h₁ S, h₂ S]
  -- RHS bookkeeping: `lift (φ S) = lift (α₁ S) + lift (α₂ S)` (via `hφhom` + `liftPointToKE_add`),
  -- and the rest is abelian regrouping.
  have hlift : liftPointToKE W (φ.toAddMonoidHom S) =
      liftPointToKE W (α₁.toAddMonoidHom S) + liftPointToKE W (α₂.toAddMonoidHom S) := by
    rw [hφhom, AddMonoidHom.add_apply, liftPointToKE_add]
  rw [hlift]
  abel

/-! ### Bridge: the canonical-action leaf from any genuine action

The `SeparableWitnesses.lean` reductions (`oneSub_hcommPrime_of_hgcomm`,
`pencil_hkerdeg_of_hgcomm_separable`, …) consume `MapTranslateGenericPoint` for the **canonical**
action `g = Affine.Point.map φ.pullback`.  Since `MapTranslateGenericPoint` only constrains the
value of the action at the single point `P_gen`, and a genuine action `g` agrees with the canonical
one there (`map_pullback_genericPoint_of_isGenuineWith`), the canonical leaf follows from the leaf
for any genuine `g`. -/

/-- **The canonical-action covariance leaf from any genuine action** (Silverman III.8.2).  For an
isogeny `φ` genuine with geometric action `g` (`IsGenuineWith W φ g`), the generic-point covariance
leaf for the **canonical** action `Affine.Point.map φ.pullback` follows from the leaf for `g`.

`MapTranslateGenericPoint` constrains only `g P_gen`, and `g P_gen = Point.map φ.pullback P_gen`
for a genuine `g` (`map_pullback_genericPoint_of_isGenuineWith`); rewriting that single equality
both occurrences turns the leaf for `g` into the leaf for the canonical action. -/
theorem mapTranslateGenericPoint_canonical_of_genuine
    (φ : Isogeny W.toAffine W.toAffine)
    {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
    (hgen : IsGenuineWith W φ g)
    (hg : MapTranslateGenericPoint W φ g) :
    MapTranslateGenericPoint W φ
      (WeierstrassCurve.Affine.Point.map (W' := W) φ.pullback) := by
  intro S
  have hbridge : WeierstrassCurve.Affine.Point.map (W' := W) φ.pullback (genericPoint W) =
      g (genericPoint W) :=
    map_pullback_genericPoint_of_isGenuineWith W φ hgen
  -- The leaf for `g` at `S`, with `g P_gen` rewritten back to the canonical `Point.map φ.pullback P_gen`.
  have hgS := hg S
  rw [← hbridge] at hgS
  exact hgS

end Additive

/-! ### The Frobenius component — the `q`-power translation commutation (the heart of the Frobenius
generic-point leaf over `K̄`)

The `1 − π = addIsog(id, −π)` and `rπ − s = addIsog(r·π, −s·id)` decompositions reduce `hgcomm` (via
`mapTranslateGenericPoint_add`) to the component leaves for `[m]` (free, `map_zsmul`) and for the
*Frobenius* `π` over `K̄`.  Over `K̄ = AlgebraicClosure 𝔽_q` the relative `q`-Frobenius is **not** a
base-field-linear map, so unlike the `[m]` case its generic-point covariance is genuine geometric
content (the project carries it as a hypothesis, e.g. `FrobeniusScalingWitnesses` in
`FrobeniusGalois.lean`).

The structural core of that content is the **commutation of the `q`-power with translation**: for the
`q`-power Frobenius `frob = FiniteField.frobeniusAlgHom 𝔽_q (K̄(E))` (the `q`-power as an `𝔽_q`-algebra
hom of the function field of `E_{K̄}`) and translation `τ_S` (an `K̄`-algebra hom, hence a ring hom),

  `frob (τ_S g) = τ_S (frob g)`   for all `g ∈ K̄(E)`,

because `(τ_S g)^q = τ_S (g^q)` (`τ_S` is a ring hom and `frob = (· ^ q)`).  Note this is the *same*
`S` on both sides at the function-field level; the geometric Frobenius twist `π̄ S` appears only when
this is combined with `frob (lift S) = lift (π̄ S)` (the `q`-power on coordinates is the geometric
Frobenius on a `K̄`-point — `geomFrobeniusPointFun_some`) inside the full generic-point leaf.

This commutation is the `K̄` analogue of the fixed-field `frobeniusIsog_pullback_universal_commute`
(`Frobenius.lean`), which does *not* apply over `K̄` (there `frob` is `K̄`-linear only on `𝔽_q`).  We
ship it here as the reusable kernel of the Frobenius component leaf. -/

section Frobenius

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [(W.baseChange L).toAffine.IsElliptic]

/-- **The `q`-power Frobenius commutes with translation on `K̄(E)`** (the kernel of the Frobenius
generic-point leaf; Silverman III.8.2 for `π` over `K̄`).  For the `q`-power `𝔽_q`-algebra Frobenius
`frob = FiniteField.frobeniusAlgHom K (K̄(E))` and the translation `τ_S` of `E_{K̄}` by any point `S`,

  `frob (τ_S g) = τ_S (frob g)`   for all `g`,

since `frob = (· ^ q)` and `τ_S` is a ring hom, so both sides are `(τ_S g)^q`.  This is the `K̄`
analogue of `frobeniusIsog_pullback_universal_commute` (which holds only over the fixed field `𝔽_q`);
combined with `frob (lift S) = lift (π̄ S)` it yields the Frobenius component of the generic-point
covariance `hgcomm`. -/
theorem frobeniusAlgHom_translate_commute
    (S : (W.baseChange L).toAffine.Point) (g : (W.baseChange L).toAffine.FunctionField) :
    (FiniteField.frobeniusAlgHom K (W.baseChange L).toAffine.FunctionField)
        (translateAlgEquivOfPoint (W.baseChange L) S g) =
      translateAlgEquivOfPoint (W.baseChange L) S
        ((FiniteField.frobeniusAlgHom K (W.baseChange L).toAffine.FunctionField) g) := by
  simp only [FiniteField.coe_frobeniusAlgHom]
  exact (map_pow (translateAlgEquivOfPoint (W.baseChange L) S) g (Fintype.card K)).symm

/-- **The `q`-power Frobenius commutes with translation, alg-hom/ring-hom form** (Silverman III.8.2
for `π` over `K̄`).  The `RingHom.comp` packaging of `frobeniusAlgHom_translate_commute`:
`frob ∘ τ_S = τ_S ∘ frob` as ring endomorphisms of `K̄(E)`.  (Phrased on `RingHom` to sidestep the
scalar mismatch: `frob` is an `𝔽_q`-algebra hom, `τ_S` an `K̄`-algebra hom.)  This is the form the
function-field functoriality `Affine.Point.map_map` consumes inside the Frobenius generic-point
leaf. -/
theorem frobeniusAlgHom_translate_commute_ringHom
    (S : (W.baseChange L).toAffine.Point) :
    (FiniteField.frobeniusAlgHom K (W.baseChange L).toAffine.FunctionField).toRingHom.comp
        (translateAlgEquivOfPoint (W.baseChange L) S).toAlgHom.toRingHom =
      (translateAlgEquivOfPoint (W.baseChange L) S).toAlgHom.toRingHom.comp
        (FiniteField.frobeniusAlgHom K (W.baseChange L).toAffine.FunctionField).toRingHom := by
  ext g
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  exact frobeniusAlgHom_translate_commute W L S g

end Frobenius

end HasseWeil.WeilPairing
