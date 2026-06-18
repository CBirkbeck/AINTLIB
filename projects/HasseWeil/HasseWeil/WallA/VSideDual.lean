/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.GapSpines
import HasseWeil.Hasse.SumTrace
import HasseWeil.Verschiebung.Genuine

/-!
# Wall A — the V-side dual route to the signed III.6.3 degree identity

This file assembles the **V-side genuine isogeny** `β_dual = r·V − s` (built on the
Verschiebung `V`, mirroring the π-side genuine `β = r·π − s`) into the pivot-chain scaffold
shipped in `HasseWeil.GapSpines`, in order to drive

  `deg(r·π − s) = q·r² − t·r·s + s²`   (the Wall-A keystone; its unconditional sorried form
  `genuineIsogSmulSub_degree_eq_signed` was retired 2026-06-11 — the witness-parametric
  `genuineIsogSmulSub_degree_eq_signed_via_walls` is the shipped form).

## What is proved here, unconditionally

* `isogeny_isGenuineWith_pointMap` — **any** isogeny `φ` is `IsGenuineWith` the geometric action
  `Affine.Point.map φ.pullback` on `(W_KE).Point`.  This is the clean, general form of the
  "the pullback is the comorphism of a geometric map" non-vacuity check (`map_some`).
* `betaDualV` — the V-side genuine isogeny `r·V − s`, constructed via the genuine-sum combinator
  `addIsog` applied to the Verschiebung (so **`addIsog` does generalise to `V`** — the V-side
  pole/injectivity bricks already live in `Verschiebung/Genuine.lean`).
* `betaDualV_toAddMonoidHom_sub` — the point-map of `betaDualV` is `r·V − s·id`
  (`h_beta_dual_hom`), using `V.toAddMonoidHom = [q]` (`verschiebungIsog_of_witness`).
* `betaDualV_isDual_pi` — `IsDualOf V π` (`h_isDual_V_pi`), from `verschiebung_dual_exists`'s
  underlying witness.
* `genuineIsogSmulSub_degree_eq_signed_closed` — the **closing lemma**: it constructs `V` and
  `β_dual = r·V − s` internally, discharges `h_isDual_V_pi`, `h_beta_dual_hom`, `h_beta_pos`, and
  reduces the Wall-A keystone to exactly the three *standing dual residuals* (the genuine III.6.1 /
  III.6.2 content the project has not yet shipped unconditionally):

    1. `h_sum_trace`  : `π + V = [t]`     (the trace relation, Silverman III.6.2(b); itself the
       output of `sum_trace_frobenius_witness` modulo `IsDualOf (1−V) (1−π)`);
    2. `h_pullback_eq`: the full-isogeny **comorphism** identity `(β_dual ∘ β)* = [N]*` (the
       "double-Vieta" pullback match — the geometrically irreducible content);
    3. `h_isDual_pair`: `IsDualOf β_dual β` (Silverman III.6.1 for the genuine pair).

  Everything else is internal; this is the honest reduction of Wall A to the standing dual
  residuals, composed through `genuineIsogSmulSub_degree_eq_signed_of_full_pivot_chain`.

The unconditional statement (the former bare-`sorry`
`GapSpines.genuineIsogSmulSub_degree_eq_signed`, deleted 2026-06-11 with the legacy skeleton
chain) would require the three residuals above unconditionally (the project has not
shipped `IsDualOf (1−V) (1−π)` nor the double-Vieta pullback identity); this
witness-parametric closing lemma is the live form.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.6.1–III.6.3.
-/

open WeierstrassCurve

namespace HasseWeil

namespace WallA

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]

/-! ### A general genuineness witness: any isogeny is genuine with `map pullback`

`IsGenuineWith φ g` (`GapSpines`) only constrains the geometric action `g` at the generic point
`P_gen = (x_gen, y_gen)`: it asks `g P_gen = some (φ.pullback x_gen) (φ.pullback y_gen)`.  For the
**canonical** action `Affine.Point.map (W' := W) φ.pullback` this is exactly `Affine.Point.map_some`
applied to `genericPoint = some x_gen y_gen _`.  So genuineness with the canonical action holds for
*every* isogeny, with no hypotheses — this is the clean non-vacuity form (it confirms `IsGenuine`
is satisfied by any genuine geometric isogeny, the pullback being its comorphism). -/
omit [Fintype K] [Fintype W.toAffine.Point] in
theorem isogeny_isGenuineWith_pointMap (φ : Isogeny W.toAffine W.toAffine) :
    IsGenuineWith W φ (WeierstrassCurve.Affine.Point.map (W' := W) φ.pullback) := by
  refine ⟨φ.pullback (x_gen W), φ.pullback (y_gen W),
    (WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine
      φ.pullback.injective (x_gen W) (y_gen W)).mpr (generic_nonsingular W), ?_, rfl, rfl⟩
  rw [genericPoint_xOf_some]
  exact WeierstrassCurve.Affine.Point.map_some (f := φ.pullback) (generic_nonsingular W)

omit [Fintype K] [Fintype W.toAffine.Point] in
/-- Every isogeny is genuine (existential form), via the canonical `map pullback` action. -/
theorem isogeny_isGenuine (φ : Isogeny W.toAffine W.toAffine) : IsGenuine W φ :=
  ⟨_, isogeny_isGenuineWith_pointMap W φ⟩

/-! ### The Verschiebung as a concrete `V` with `IsDualOf V π`

We pin a single concrete Verschiebung witness, `verschiebungV`, from the connected (axiom-clean
modulo the upstream `[q] = V ∘ π` factorisation) inclusion `mulByInt_q_pullback_subset_frobenius`.
Its `IsDualOf V π` is `verschiebung_dual_exists`'s underlying witness, and its point map is the
`[q]`-point map (`verschiebungIsog_of_witness.toAddMonoidHom = (mulByInt q).toAddMonoidHom`). -/

/-- The inclusion `Im([q]*) ⊆ Im(π*)` (Silverman II.2.11/III.6.2), the connected witness. -/
noncomputable abbrev hSubset (hq : 2 ≤ Fintype.card K) :
    (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
      (frobeniusIsog W).pullback.range :=
  mulByInt_q_pullback_subset_frobenius W hq

/-- The concrete Verschiebung `V` (dual to the `q`-power Frobenius `π`). -/
noncomputable def verschiebungV (hq : 2 ≤ Fintype.card K) :
    Isogeny W.toAffine W.toAffine :=
  verschiebungIsog_of_witness W (hSubset W hq)

/-- `IsDualOf V π` for the concrete Verschiebung (`h_isDual_V_pi`, Silverman III.6.1 Case 2). -/
theorem verschiebungV_isDual (hq : 2 ≤ Fintype.card K) :
    IsDualOf W.toAffine (verschiebungV W hq) (frobeniusIsog W) :=
  verschiebungIsog_of_witness_isDualOf_frobenius W (hSubset W hq)

/-- The point map of the concrete Verschiebung is the `[q]`-point map (`= q • ·`).  Frobenius on
`F_q`-rational points is the identity, so the dual `V` (`V ∘ π = [q]`) must carry the `[q]`-point
map. -/
@[simp] theorem verschiebungV_toAddMonoidHom (hq : 2 ≤ Fintype.card K) :
    (verschiebungV W hq).toAddMonoidHom =
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).toAddMonoidHom :=
  rfl

/-! ### The V-side genuine isogeny `β_dual = r·V − s`

This is `addIsog` of the genuine pair `(V.zsmul r, [−s])` — the **exact mirror** of the π-side
`genuineIsogSmulSub = addIsog (π.zsmul r, [−s])`.  So `addIsog` *does* generalise to `V`: the V-side
non-inverse / injectivity / pole bricks are the ones shipped in `Verschiebung/Genuine.lean`
(`genuineIsogSmulSubV_universal_unconditional`).  Its point map is `r·V + (−s) = r·V − s`. -/

/-- The V-side genuine isogeny `r·V − s` on the concrete Verschiebung `V`. -/
noncomputable def betaDualV (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    Isogeny W.toAffine W.toAffine :=
  genuineIsogSmulSubV_universal_unconditional W (verschiebungV W hq)
    (verschiebungV_isDual W hq) r s hr hs hrK hsK

/-- The point map of `betaDualV` is `r·V − s·id` (`h_beta_dual_hom`).

`betaDualV.toAddMonoidHom = (V.zsmul r) + [−s]`, and `(V.zsmul r) = [r] ∘ V`, so pointwise this is
`r • V P + (−s) • P = r • V P − s • P`, i.e. `r • V.toAddMonoidHom − s • id`. -/
theorem betaDualV_toAddMonoidHom_sub (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (betaDualV W hq r s hr hs hrK hsK).toAddMonoidHom =
      r • (verschiebungV W hq).toAddMonoidHom - s • (AddMonoidHom.id _) := by
  -- `betaDualV` unfolds (via the V-side universal constructor) to `addIsog (V.zsmul r) [−s]`,
  -- whose `toAddMonoidHom` is `(V.zsmul r).toAddMonoidHom + (mulByInt -s).toAddMonoidHom`.  The
  -- internally-produced `verschiebungIsog_of_witness W _` is, by proof irrelevance on its `h_subset`
  -- argument, the same as `verschiebungV W hq`.
  show ((verschiebungV W hq).zsmul r).toAddMonoidHom +
      (mulByInt W.toAffine (-s)).toAddMonoidHom = _
  ext P
  simp only [AddMonoidHom.add_apply, AddMonoidHom.sub_apply, AddMonoidHom.smul_apply,
    AddMonoidHom.id_apply, Isogeny.zsmul_apply, mulByInt_apply]
  rw [neg_smul, sub_eq_add_neg]

/-! ### The Wall-A keystone, reduced to the standing dual residuals

`genuineIsogSmulSub_degree_eq_signed_closed` is the live, witness-parametric form of the Wall-A
keystone (whose unconditional sorried form was deleted 2026-06-11).  It constructs the concrete Verschiebung
`V` and the V-side genuine isogeny `β_dual = r·V − s` internally, discharges the three *structural*
pivot inputs (`h_isDual_V_pi`, `h_beta_dual_hom`, `h_beta_pos`), and reduces the keystone to exactly
the three **standing dual residuals** plus the nonvanishing of `N`:

* `h_sum_trace`  — the trace relation `π + V = [t]` (Silverman III.6.2(b); the output of
  `sum_trace_frobenius_witness` once `IsDualOf (1−V) (1−π)` ships);
* `h_pullback_eq` — the comorphism identity `(β_dual ∘ β)* = [N]*` (the double-Vieta pullback match,
  the geometrically irreducible content of Wall A — equivalently, that `β_dual ∘ β` is genuine with
  the `[N]` action; see `GapSpines.genuine_dual_comp_eq_mulByInt_of_isGenuineWith`);
* `h_isDual_pair` — `IsDualOf β_dual β` (Silverman III.6.1 for the genuine pair);
* `h_N_ne`        — `N = q·r² − t·r·s + s² ≠ 0` (automatic in the Hasse assembly: `β_dual ∘ β = [N]`
  forces `deg β · deg β_dual = N²`, so `N ≠ 0`; carried here as a hypothesis).

The composition is `genuineIsogSmulSub_degree_eq_signed_of_full_pivot_chain` (GapSpines), with the
internally-built `V = verschiebungV`, `β_dual = betaDualV`.  This is the honest reduction of Wall A:
the only inputs are the genuine III.6.1/III.6.2 facts the project has not yet shipped
unconditionally. -/
theorem genuineIsogSmulSub_degree_eq_signed_closed (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + (verschiebungV W hq).toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_pullback_eq :
      ((betaDualV W hq r s hr hs hrK hsK).comp
          (genuineIsogSmulSub W r s hr hs hrK hsK)).pullback =
      (mulByInt W.toAffine
        ((Fintype.card K : ℤ) * r ^ 2 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)).pullback)
    (h_isDual_pair :
      IsDualOf W.toAffine (betaDualV W hq r s hr hs hrK hsK)
        (genuineIsogSmulSub W r s hr hs hrK hsK))
    (h_N_ne : (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 ≠ 0) :
    ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 :=
  genuineIsogSmulSub_degree_eq_signed_of_full_pivot_chain W hq r s hr hs hrK hsK
    (verschiebungV W hq) (betaDualV W hq r s hr hs hrK hsK)
    (verschiebungV_isDual W hq)
    h_sum_trace
    (betaDualV_toAddMonoidHom_sub W hq r s hr hs hrK hsK)
    h_pullback_eq
    h_isDual_pair
    (genuineIsogSmulSub_degree_pos W r s hr hs hrK hsK)
    h_N_ne

end WallA

end HasseWeil
