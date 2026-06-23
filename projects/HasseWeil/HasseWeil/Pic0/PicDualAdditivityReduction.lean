import HasseWeil.Pic0.PicDual
import HasseWeil.AdditionPullback.Frobenius

/-!
# Route C — dual additivity for the Frobenius family (Silverman III.6.2(c) / III.8)

This file attacks the **single irreducible residual** of Route C: the Silverman III.6.2(c)
dual-additivity instance

  `picDual((rπ) + (−s)) = picDual(rπ) + picDual(−s)`            (point maps on `E.Point`),

equivalently the Silverman III.8 trace relation for the whole `α = rπ − s`,

  `(rπ − s) + picDual(rπ − s) = [r·t − 2s]`                     (`htrace_dual`),

which `RouteCGeometric.degree_eq_N_via_picDual_geometric_hpicval_discharged` consumes as its last
opaque input.  Per the task constraints we work in a **new file** and import what we need from
`PicDual.lean` and `AdditionPullback/Frobenius.lean`; we do **not** edit `PicDual.lean` or
`RouteCGeometric.lean`.

## What is genuinely hard here (Silverman III.6.2(c), verified vs the in-repo PDF p.84)

In the Pic⁰ framework of `PicDual.lean`, `picDual α = κ⁻¹ ∘ classMap_α ∘ κ` with
`κ = toClassEquiv'` and `classMap_α = ClassGroup.map (α*)` the **ideal extension** of the *specific*
comorphism `α* : R → R` (`R = E.CoordinateRing`).  Dual additivity is therefore equivalent to

  `classMap_{α+β} = classMap_α ⋆ classMap_β`     (product of `ClassGroup`-monoid-homs),

transported through `κ` to the `Additive (ClassGroup R)` addition.  This identity is **false at the
comorphism level**: the comorphism of `α + β` is governed by the **addition formula** on `E`
(`AdditionPullback/*`, the theorem of the cube), *not* by the product of the individual comorphisms
`α*`, `β*`.  This is exactly why Silverman III.6.2(c) proves `(φ+ψ)^ = φ̂ + ψ̂` via a `Div⁰`
(degree-0 divisor / function) argument using the addition formula — it is **not** a structural fact
about ideal extension.  Concretely: `isogTrace α one_sub_α = 1 + deg α − deg(1 − α)` is a *quadratic
form* in `α` (Silverman III.6.3), so `tr` is **not** additive in general either; the "trace-witness"
route (`DualIsogeny.dual_add_of_trace_witnesses`) takes the `α + β` trace identity as an *input*
precisely because deriving it is the same III.6.2(c) content.

## What this file ships (genuine, non-circular, axiom-clean)

The residual does **not** close structurally.  We ship a precise, non-circular **reduction chain**
that pins down the irreducible content as sharply as possible:

* `htrace_dual_iff_picDual_eq_rV_sub_s` — the **trace ⟺ picDual-value equivalence**: for the
  `rπ − s` shape with `π + V = [t]`, the III.8 trace relation `htrace_dual` is *equivalent* (both
  directions, pure point-group algebra, no degree, **non-circular**) to the dual-additivity output
  `picDual(rπ − s) = r·V − s`.  This is the algebraic backbone of Part (B) v3.

* `htrace_dual_of_picDual_additive` — the **abstract dual-additivity engine**: given the single
  III.6.2(c) hypothesis `picDual α = picDual α₁ + picDual α₂` at the point-map level (with
  `α.toAddMonoidHom = α₁.toAddMonoidHom + α₂.toAddMonoidHom`) **and** the two shipped per-summand
  `picDual` values `picDual α₁ = r·V`, `picDual α₂ = −s·id`, derive `htrace_dual`.  This **converts**
  the III.8-trace residual into the single cleanest possible residual — *pointwise additivity of
  `picDual` on the fixed two-term decomposition `rπ + [−s]`* — and discharges everything else
  non-circularly.

* `picDual_eq_rV_sub_s_of_additive` — the same engine in **picDual-value form**, delivering the
  III.6.2(c) dual value `α̂ = r·V − s·id` directly (the form Route-C Part (B) v3 ultimately wants)
  from the two seeds (`picDual α₁ = r·V`, `picDual α₂ = −s·id`) **plus** the single named additivity
  residual `hadd` (`hbeta`/`hsum` are not needed for the purely-value conclusion).

## The precise remaining lemma (the irreducible sub-decomposition)

After this file, `htrace_dual` reduces to the **one** lemma

  `hadd :  α.picDual ch hinj hfin
            = α₁.picDual ch₁ hinj₁ hfin₁ + α₂.picDual ch₂ hinj₂ hfin₂`

for `α₁ = (frobeniusIsog W).zsmul r`, `α₂ = mulByInt W.toAffine (−s)`, `α = α₁ ⊞ α₂` (point-map
sum).  In Pic⁰ terms this is `classMap_α = classMap_{α₁} ⋆ classMap_{α₂}` transported through `κ`.
It is **Silverman III.6.2(c)** for this pair and needs the `Div⁰`/addition-formula argument: the
machinery is the project's addition-formula pullback (`AdditionPullback/Frobenius.lean`,
`addPullbackAlgHomPair`, `mk_XYIdeal'_mul_mk_XYIdeal'`) feeding the theorem-of-the-cube linearity of
the divisor-class pullback on `Pic⁰`.  It is **not** circular with `deg(rπ − s) = N` (it never
mentions that degree), but it is **not** structural in the ideal-extension framework, which is why it
is the genuine irreducible residual.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.6.2(c) (PDF p.84), III.6.3 (degree QF),
  III.8 (trace).  Verified against the in-repo PDF (offset +18).
-/

open WeierstrassCurve
open scoped nonZeroDivisors

namespace HasseWeil.Pic0.RouteCAdditivity

/-! ### Phase 1 — the trace ⟺ picDual-value equivalence (abstract, non-circular)

The Silverman III.8 trace relation for an endomorphism `α` of `rπ − s` shape *determines* its dual
value, and conversely.  Working purely at the **point-group** level (`AddMonoidHom` on `E.Point`),
with abstract point endomorphisms `π, V` satisfying the Frobenius trace relation `π + V = [t]`
(`hsum`), the III.8 relation

  `α + α̂ = [r·t − 2s]`              (`htrace_dual`)

is **equivalent** to the dual-additivity output

  `α̂ = r·V − s·id`                 (`hpicval`).

Both directions are pure left-cancellation against the non-circular candidate identity
`(rπ − s) + (rV − s) = [r·t − 2s]` (`PicDual.smul_sub_add_smul_sub_eq_mulByInt`, derived from `hsum`
alone — *no degree, no uniqueness*).  This is the algebraic backbone of Route-C Part (B) v3: it shows
the III.8 residual and the III.6.2(c) dual-value are literally the same content up to the shipped
trace half. -/

variable {F : Type*} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F} [E.IsElliptic]

/-- **The candidate trace half is an `AddMonoidHom`-level identity** (re-export of the shipped
`PicDual.smul_sub_add_smul_sub_eq_mulByInt` under the local names): for abstract point endomorphisms
`π, V` with `π + V = [t]`,

  `(r·π − s·id) + (r·V − s·id) = [r·t − 2s]`.

Pure point-group algebra from `hsum`; carries no `picDual`, no degree — **non-circular**. -/
theorem smul_sub_add_smul_sub_eq
    {π V : E.Point →+ E.Point} (r s t : ℤ)
    (hsum : π + V = (mulByInt E t).toAddMonoidHom) :
    (r • π - s • (AddMonoidHom.id _)) + (r • V - s • (AddMonoidHom.id _)) =
      (mulByInt E (r * t - 2 * s)).toAddMonoidHom :=
  HasseWeil.Isogeny.smul_sub_add_smul_sub_eq_mulByInt r s t hsum

/-- **III.8 trace ⟹ III.6.2(c) dual value** (point maps, non-circular).

Given the `rπ − s` shape (`hbeta`), the Frobenius trace relation `π + V = [t]` (`hsum`) and the
III.8 relation `α + α̂ = [r·t − 2s]` (`htrace_dual`), the dual value is `α̂ = r·V − s·id`.

This is the existing `PicDual.picDual_eq_smul_sub_of_sum_trace`, exposed under the equivalence
framing.  It subtracts `α` from both `htrace_dual` and the candidate half, then left-cancels. -/
theorem picDual_eq_of_htrace_dual
    {α : Isogeny E E} (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    {π V : E.Point →+ E.Point} (r s t : ℤ)
    (hbeta : α.toAddMonoidHom = r • π - s • (AddMonoidHom.id _))
    (hsum : π + V = (mulByInt E t).toAddMonoidHom)
    (htrace_dual : α.toAddMonoidHom + α.picDual ch hinj hfin =
      (mulByInt E (r * t - 2 * s)).toAddMonoidHom) :
    α.picDual ch hinj hfin = r • V - s • (AddMonoidHom.id _) :=
  HasseWeil.Isogeny.picDual_eq_smul_sub_of_sum_trace ch hinj hfin r s t hbeta hsum htrace_dual

/-- **III.6.2(c) dual value ⟹ III.8 trace** (point maps, non-circular — the converse direction).

The reverse implication: if the dual value is `α̂ = r·V − s·id` (`hpicval`, the III.6.2(c) output),
then the III.8 trace relation `α + α̂ = [r·t − 2s]` holds.  Obtained by rewriting `α̂` via `hpicval`
and `α` via `hbeta`, then applying the non-circular candidate half `smul_sub_add_smul_sub_eq`.

Together with `picDual_eq_of_htrace_dual` this gives the **equivalence** `htrace_dual ⟺ hpicval`. -/
theorem htrace_dual_of_picDual_eq
    {α : Isogeny E E} (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    {π V : E.Point →+ E.Point} (r s t : ℤ)
    (hbeta : α.toAddMonoidHom = r • π - s • (AddMonoidHom.id _))
    (hsum : π + V = (mulByInt E t).toAddMonoidHom)
    (hpicval : α.picDual ch hinj hfin = r • V - s • (AddMonoidHom.id _)) :
    α.toAddMonoidHom + α.picDual ch hinj hfin =
      (mulByInt E (r * t - 2 * s)).toAddMonoidHom := by
  rw [hbeta, hpicval]
  exact smul_sub_add_smul_sub_eq r s t hsum

/-- **The III.8 ⟺ III.6.2(c) equivalence, packaged** (point maps, non-circular).

For the `rπ − s` shape with the Frobenius trace relation `π + V = [t]`, the III.8 trace relation
`α + α̂ = [r·t − 2s]` is **equivalent** to the III.6.2(c) dual value `α̂ = r·V − s·id`.  Pure
point-group algebra from `hsum` (`smul_sub_add_smul_sub_eq`) — **no degree, no uniqueness, no
circularity with `deg(rπ − s) = N`**.  This pins the irreducible Route-C residual: closing *either*
side closes the other, and both are exactly Silverman III.6.2(c) for `α = rπ − s`. -/
theorem htrace_dual_iff_picDual_eq_rV_sub_s
    {α : Isogeny E E} (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    {π V : E.Point →+ E.Point} (r s t : ℤ)
    (hbeta : α.toAddMonoidHom = r • π - s • (AddMonoidHom.id _))
    (hsum : π + V = (mulByInt E t).toAddMonoidHom) :
    (α.toAddMonoidHom + α.picDual ch hinj hfin =
        (mulByInt E (r * t - 2 * s)).toAddMonoidHom) ↔
      α.picDual ch hinj hfin = r • V - s • (AddMonoidHom.id _) :=
  ⟨fun htrace_dual ↦ picDual_eq_of_htrace_dual ch hinj hfin r s t hbeta hsum htrace_dual,
   fun hpicval ↦ htrace_dual_of_picDual_eq ch hinj hfin r s t hbeta hsum hpicval⟩

/-! ### Phase 2 — the abstract dual-additivity engine (reduce III.8 to the additivity residual)

We now make the **III.6.2(c) additivity** the single explicit input and *derive* `htrace_dual` from
it together with the two shipped per-summand `picDual` seeds.  The endomorphism `α` is given as a
**point-map sum** `α.toAddMonoidHom = α₁.toAddMonoidHom + α₂.toAddMonoidHom` (`hsumhom`; for the
Route-C `α = rπ − s` this holds by `rfl` via `genuineIsogSmulSub_toAddMonoidHom`), with `α₁ = rπ`
and `α₂ = [−s]`.

The single III.6.2(c) hypothesis is

  `hadd :  α.picDual ch hinj hfin = α₁.picDual ch₁ hinj₁ hfin₁ + α₂.picDual ch₂ hinj₂ hfin₂`.

The two seeds are `picDual α₁ = r·V` (`Isogeny.picDual_zsmul_eq_zsmul_of_isDual`, non-circular via
`deg(rπ) = r²q`) and `picDual α₂ = −s·id` (`picDual_mulByInt_eq_self`, non-circular via
`deg[−s] = s²`).  Everything below `hadd` is non-circular point-group algebra. -/

/-- **Abstract dual-additivity engine: `htrace_dual` from the additivity residual + the two seeds.**

Inputs (all at the **point-map** level over `E.Point`):
* `hsumhom`  — `α` is the point-map sum of two summands `α₁`, `α₂`;
* `hbeta`    — `α` has the `r·π − s·id` shape;
* `hsum`     — the Frobenius trace relation `π + V = [t]`;
* `hdual₁`   — the seed `picDual α₁ = r·V` (= `α₁̂`);
* `hdual₂`   — the seed `picDual α₂ = −s·id` (= `α₂̂`);
* `hadd`     — the **single III.6.2(c) residual** `picDual α = picDual α₁ + picDual α₂`.

Output: the Silverman III.8 trace relation `α + α̂ = [r·t − 2s]` (`htrace_dual`).

Proof: `hadd` + the two seeds give `α̂ = r·V + (−s·id) = r·V − s·id`, which is `hpicval`; then the
non-circular converse `htrace_dual_of_picDual_eq` upgrades it to the III.8 relation.  **No degree of
`α`, no uniqueness, no circularity with `deg(rπ − s) = N`** — the only non-structural input is `hadd`
(Silverman III.6.2(c) for this pair). -/
theorem htrace_dual_of_picDual_additive
    {α α₁ α₂ : Isogeny E E}
    (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (ch₁ : α₁.CoordHom) (hinj₁ : Function.Injective ch₁.toAlgHom)
    (hfin₁ : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch₁.toAlgebra.toModule)
    (ch₂ : α₂.CoordHom) (hinj₂ : Function.Injective ch₂.toAlgHom)
    (hfin₂ : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch₂.toAlgebra.toModule)
    {π V : E.Point →+ E.Point} (r s t : ℤ)
    (hbeta : α.toAddMonoidHom = r • π - s • (AddMonoidHom.id _))
    (hsum : π + V = (mulByInt E t).toAddMonoidHom)
    (hdual₁ : α₁.picDual ch₁ hinj₁ hfin₁ = r • V)
    (hdual₂ : α₂.picDual ch₂ hinj₂ hfin₂ = -(s • (AddMonoidHom.id _)))
    (hadd : α.picDual ch hinj hfin =
      α₁.picDual ch₁ hinj₁ hfin₁ + α₂.picDual ch₂ hinj₂ hfin₂) :
    α.toAddMonoidHom + α.picDual ch hinj hfin =
      (mulByInt E (r * t - 2 * s)).toAddMonoidHom := by
  -- `hadd` + the two seeds collapse `α̂` to the III.6.2(c) value `r·V − s·id`.
  have hpicval : α.picDual ch hinj hfin = r • V - s • (AddMonoidHom.id _) := by
    rw [hadd, hdual₁, hdual₂, sub_eq_add_neg]
  -- The non-circular converse upgrades the dual value to the III.8 trace relation.
  exact htrace_dual_of_picDual_eq ch hinj hfin r s t hbeta hsum hpicval

/-- **Abstract dual-additivity engine, picDual-value form.**

As `htrace_dual_of_picDual_additive`, but delivering the III.6.2(c) **dual value**
`α̂ = r·V − s·id` directly (the form Route-C Part (B) v3 ultimately wants, equivalent to the III.8
relation by Phase 1).  Needs only the additivity residual `hadd` and the two seeds — `hbeta`/`hsum`
are not required for this purely-value conclusion. -/
theorem picDual_eq_rV_sub_s_of_additive
    {α α₁ α₂ : Isogeny E E}
    (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (ch₁ : α₁.CoordHom) (hinj₁ : Function.Injective ch₁.toAlgHom)
    (hfin₁ : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch₁.toAlgebra.toModule)
    (ch₂ : α₂.CoordHom) (hinj₂ : Function.Injective ch₂.toAlgHom)
    (hfin₂ : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch₂.toAlgebra.toModule)
    {V : E.Point →+ E.Point} (r s : ℤ)
    (hdual₁ : α₁.picDual ch₁ hinj₁ hfin₁ = r • V)
    (hdual₂ : α₂.picDual ch₂ hinj₂ hfin₂ = -(s • (AddMonoidHom.id _)))
    (hadd : α.picDual ch hinj hfin =
      α₁.picDual ch₁ hinj₁ hfin₁ + α₂.picDual ch₂ hinj₂ hfin₂) :
    α.picDual ch hinj hfin = r • V - s • (AddMonoidHom.id _) := by
  rw [hadd, hdual₁, hdual₂, sub_eq_add_neg]

end HasseWeil.Pic0.RouteCAdditivity
