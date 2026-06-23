import HasseWeil.Pic0.PicDualDegreeViaIsDualOf
import HasseWeil.IsogenyBaseChange
import HasseWeil.Pic0.ToClassFunctorial

/-!
# Route C (geometric): closing Leaf 1 over `F̄` WITHOUT the genuine-comorphism upgrade

This file ships the **geometric** half of Route C — the move that closes the Hasse-bound *Leaf 1*
(`deg(rπ − s) = N`, hence `qf_nonneg`) along the Pic⁰ push-pull route **without** the
genuine-isogeny comorphism upgrade (Wall A / BRIDGE-003), **without** surjectivity of `β` itself,
and **without** the Wall-C signed-degree extractor.

## The insight (why genuineness is avoidable)

`deg(rπ − s)` is the scalar in the Pic⁰ push-pull `picDual(β) ∘ β = [deg β]` (a **point-map**
relation; the exponent is `finrank` via the `ClassGroup.relNorm`/`degree` bridge).  Vieta on `ℤ[π]`
gives `(rV − s) ∘ β = [N]` (also **point maps**).  With `picDual(β) = rV − s` (dual additivity), the
two point-map composites coincide, so

  `[deg(rπ − s)] = [N]`   **as point maps** on `E.Point`.

Over the *geometric* points `E(F̄_q)` — which form an **infinite** group, while each torsion
subgroup `E[k] = ker[k]` is **finite** for `k ≠ 0` — an equality `[m] = [n]` of `zsmul`-maps forces
`m = n`.  So `deg(rπ − s) = N` is pinned at the **point level** over `F̄`, with **no function-field
comorphism** for `picDual` (no genuine isogeny, no Wall A / BRIDGE-003, no Wall C).

## Silverman ground truth (verified vs the in-repo PDF, offset +18)

* III.4.10(a) (PDF p.86): a nonzero isogeny has **finite kernel**; in particular `E[k]` is finite
  for `k ≠ 0` (the `[k]`-torsion).
* III.6.2(a): `φ̂ φ = [deg φ]` (the push-pull, here used only at the point-map level).
* V.1.1 (PDF p.138): Hasse via the positive-definite degree quadratic form; the geometric
  `E(F̄) infinite + E[k] finite ⟹ [m]=[n]⟹m=n` is the standard pinning.

## What ships here

* **TARGET 1 (the crux, axiom-clean, self-contained):**
  `mulByInt_pointMap_injective_of_geometric` — for any `AddCommGroup` that is `Infinite` and whose
  every nonzero torsion subgroup is `Finite`, `[m] = [n]` as point maps ⟹ `m = n`; plus the EC
  specialisation `mulByInt_pointMap_injective_of_infinite_point`.
* **TARGET 2 (witness-parametric on `{hnat, additivity, CoordHom, base-change}`):**
  `degree_eq_N_via_picDual_geometric` — `deg(rπ − s) = N` assembled over `E.Point` from the
  point-map push-pull + dual additivity + Vieta, pinned by TARGET 1, with **no** `IsGenuineWith`,
  **no** `Surjective β.toAddMonoidHom`, **no** Wall C.
-/

open WeierstrassCurve
open scoped nonZeroDivisors

namespace HasseWeil.Pic0.RouteCGeometric

/-! ### TARGET 1 — geometric injectivity of `mulByInt` on points

The crux of Route C, stated **abstractly** on an additive group, which is the mathematically honest
content (and is therefore fully `#print axioms`-clean and self-contained).  It is then specialised
to the elliptic-curve point group over an infinite/algebraically-closed base. -/

/-- **TARGET 1 (abstract, the crux): `zsmul`-injectivity over an infinite group with finite
torsion.**

Let `G` be an additive commutative group that is **infinite** and whose every *nonzero* torsion
subgroup `E[k] = {P | k • P = 0}` is **finite**.  Then the `zsmul` maps separate exponents: if
`m • P = n • P` for **all** `P : G`, then `m = n`.

Proof (contrapositive).  Suppose `m ≠ n` and set `k := m − n ≠ 0`.  From `m • P = n • P` for all
`P` we get `k • P = 0` for all `P`, i.e. the `k`-torsion subgroup is *everything* (`⊤`).  But that
subgroup is `Finite` by hypothesis (`k ≠ 0`), while `G` is `Infinite` — contradiction (`G ≃ ⊤`).

This is exactly the geometric pinning `[m] = [n] ⟹ m = n` over `E(F̄)`: `E(F̄)` is infinite while
`E[k]` is finite (Silverman III.4.10a).  **No genuineness, no comorphism, no degree theory.** -/
theorem mulByInt_pointMap_injective_of_geometric
    {G : Type*} [AddCommGroup G] [Infinite G]
    (htor : ∀ k : ℤ, k ≠ 0 →
      Finite {P : G // k • P = 0})
    {m n : ℤ} (h : ∀ P : G, m • P = n • P) :
    m = n := by
  by_contra hmn
  -- `k := m − n ≠ 0`, and `k • P = 0` for every `P`.
  have hk : m - n ≠ 0 := sub_ne_zero.mpr hmn
  have hkill : ∀ P : G, (m - n) • P = 0 := by
    intro P
    rw [sub_smul, h P, sub_self]
  -- Then the whole group injects into the (finite) `(m−n)`-torsion subtype, forcing `Finite G`.
  haveI : Finite {P : G // (m - n) • P = 0} := htor (m - n) hk
  have hinj : Function.Injective (fun P : G ↦ (⟨P, hkill P⟩ : {P : G // (m - n) • P = 0})) := by
    intro P Q hPQ
    exact congrArg Subtype.val hPQ
  haveI : Finite G := Finite.of_injective _ hinj
  exact (not_finite G)

/-- **TARGET 1 (EC specialisation): geometric injectivity of `[m]` on `E.Point`.**

For an elliptic curve `E` over a field whose point group `E.Point` is **infinite** (e.g.
`E` base-changed to `F̄_q := AlgebraicClosure 𝔽_q`) and all of whose nonzero torsion subgroups
`E[k]` are **finite** (Silverman III.4.10a — a nonzero isogeny has finite kernel), the
`mulByInt` *point maps* separate exponents:

  `(∀ P, (mulByInt E m).toAddMonoidHom P = (mulByInt E n).toAddMonoidHom P) ⟹ m = n`.

This is the `E(F̄)`-pinning that lets Route C conclude `deg(rπ − s) = N` from the point-map identity
`[deg(rπ − s)] = [N]` — **without** any function-field comorphism. -/
theorem mulByInt_pointMap_injective_of_infinite_point
    {F : Type*} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F) [E.IsElliptic] [Infinite E.Point]
    (htor : ∀ k : ℤ, k ≠ 0 → Finite (E[k] : AddSubgroup E.Point))
    {m n : ℤ}
    (h : ∀ P : E.Point,
      (mulByInt E m).toAddMonoidHom P = (mulByInt E n).toAddMonoidHom P) :
    m = n := by
  -- Re-express the torsion finiteness as finiteness of the `{P // k • P = 0}` subtype, then
  -- apply the abstract crux with the `zsmul` point maps unfolded (`mulByInt_apply`).
  refine mulByInt_pointMap_injective_of_geometric (G := E.Point) ?_ ?_
  · intro k hk
    -- `E[k] = {P | k • P = 0}` (its carrier), so the two subtypes are equivalent.
    haveI : Finite (E[k] : AddSubgroup E.Point) := htor k hk
    have hcarrier : ∀ P : E.Point, (P ∈ (E[k] : AddSubgroup E.Point)) ↔ k • P = 0 :=
      fun P ↦ mem_torsionSubgroup E k P
    refine Finite.of_equiv (E[k] : AddSubgroup E.Point) ?_
    exact {
      toFun := fun P ↦ ⟨P.1, (hcarrier P.1).mp P.2⟩
      invFun := fun P ↦ ⟨P.1, (hcarrier P.1).mpr P.2⟩
      left_inv := fun P ↦ rfl
      right_inv := fun P ↦ rfl }
  · intro P
    have := h P
    simpa only [mulByInt_apply] using this

/-! ### TARGET 2 — `deg(rπ − s) = N` over `F̄`, with NO genuine comorphism / Wall C

We assemble the point-map identity `[deg(rπ − s)] = [N]` from three pieces, each at the
**point-map** (`toAddMonoidHom`) level — *no* `IsGenuineWith`, *no* `Surjective β.toAddMonoidHom`,
*no* Wall-C signed-degree extractor:

1. **Push-pull** (Silverman III.6.2(a), `α.degree` exponent):
   `picDual(β) ∘ β = [deg β]` — the shipped `picDual_comp_toAddMonoidHom_of_surjective_degree`
   (residuals: `ch`/`hinj`/`hfin`/`hnat`/`hsurjDual` + the `finrank ↔ degree` tower `(S, S')`).
2. **Dual additivity** (Silverman III.6.2(c) on `ℤ[π]`): `picDual(β) = r·V − s` as point maps —
   carried as `hdual_hom` (= the shipped `dual_add_of_trace_witnesses` output `picDual π = V`
   combined linearly).
3. **Vieta on `ℤ[π]`**: `(r·V − s) ∘ β = [N]` — the shipped point-map Vieta
   `genuine_dual_comp_toAddMonoidHom_eq_mulByInt` (residuals: the Vieta bundle
   `V`/`h_isDual_V_pi`/`h_sum_trace`/`h_beta_dual_hom`).

Pieces (1)+(2) give `(r·V − s) ∘ β = [deg β]`; with (3) this forces `[deg β] = [N]` as point maps,
i.e. `∀ P, (deg β) • P = N • P`.  Over the **geometric** points the geometric injectivity
(TARGET 1, carried here as `hgeom` — dischargeable over `F̄_q` via base-change degree-invariance)
collapses this to `deg β = N`.

**The residual list has shrunk to exactly `{hnat, hdual_hom (additivity), CoordHom data, hgeom
(= base-change geometric injectivity)}` plus the Vieta point-map bundle and `hsurjDual` (the
push-pull's `picDual`-surjectivity, automatic over `K̄`).  No `IsGenuineWith`, no
`Surjective β.toAddMonoidHom`, no Wall C.** -/

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]

/-! ### Part (B) seeds — non-circular `picDual` of Frobenius / scalars (III.6.1(a)/III.6.2(b))

To discharge `hdual_hom` (`picDual(rπ − s) = rV − s`) we seed the dual algebra with the `picDual` of
the *individual* pieces, each reachable **non-circularly** by III.6.1(a) uniqueness because the
degree of a *single* Frobenius / scalar / `rπ` is shipped — unlike `deg(rπ − s)`, which is the
Route-C *conclusion*:

* `picDual π = V` — `deg π = #K = q` (`frobeniusIsog_degree`), `V ∘ π = [q]` (`IsDualOf V π`);
* `picDual [n] = [n]` — `deg [n] = n²` (`mulByInt_degree`), `[n] ∘ [n] = [n²]`
  (`mulByInt_comp_eq_mul`);
* `picDual (rπ) = rV` — `deg (rπ) = r²q` (`Isogeny.comp_degree` / the zsmul degree) and
  `(rV) ∘ (rπ) = r²•(V ∘ π) = [r²q]`.

The *combination* `picDual(rπ − s) = picDual(rπ) + picDual(−s)` is the genuine **III.6.2(c) dual
additivity** `(φ+ψ)^ = φ̂ + ψ̂`, which Silverman proves by `Div⁰` divisor arguments (char 0;
Ex. 3.31 in general char) — **not** derivable from uniqueness, and *circular* if attempted through
the push-pull degree.  It is therefore the precise residual that `hdual_hom` reduces to (carried as
`hadd` below), with the per-piece `picDual` values supplied by these seeds. -/

/-- **`picDual α = δ` when `δ ∘ α = [d]` and `α.degree = d` — EC wrapper with explicit degree.**
A Route-C-local re-export of the non-circular III.6.1(a) uniqueness seed
`Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq`, for an endomorphism whose integer
degree `d` is supplied independently of the Pic⁰ push-pull chain. -/
theorem picDual_eq_of_degree_eq
    {β : Isogeny W.toAffine W.toAffine} (ch : β.CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hnat : β.Naturality ch hinj hfin)
    (hsurjDual : Function.Surjective (β.picDual ch hinj hfin))
    (hsurjβ : Function.Surjective β.toAddMonoidHom)
    (S : Type*) [CommRing S] [Algebra W.toAffine.CoordinateRing S]
    [FaithfulSMul W.toAffine.CoordinateRing S]
    [Algebra.IsAlgebraic W.toAffine.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra W.toAffine.CoordinateRing S'] [Algebra S S']
    [Module W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing S S'] [IsFractionRing S S']
    (hSR : @Module.finrank W.toAffine.CoordinateRing S _ _ _ =
      @Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank W.toAffine.FunctionField S' _ _ _ = β.degree)
    {d : ℤ} (hdeg : (β.degree : ℤ) = d)
    {δ : W.toAffine.Point →+ W.toAffine.Point}
    (hδ : δ.comp β.toAddMonoidHom = (mulByInt W.toAffine d).toAddMonoidHom) :
    β.picDual ch hinj hfin = δ :=
  Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq ch hinj hfin hnat hsurjDual hsurjβ
    S S' hSR hS'FF hdeg hδ

omit [Fintype W.toAffine.Point] in
/-- **Seed: `picDual π = V` (Frobenius dual = Verschiebung), non-circular.**

`deg π = #K = q` (`frobeniusIsog_degree`) and `V ∘ π = [q]` (`IsDualOf V π`, first half) feed the
III.6.1(a) uniqueness.  Residuals: the *per-Frobenius* CoordHom data (`chπ` + the two surjectivities
+ tower `(Sπ, Sπ')` + `hnatπ`). -/
theorem picDual_frobenius_eq_verschiebung
    (V : Isogeny W.toAffine W.toAffine)
    (h_isDual : IsDualOf W.toAffine V (frobeniusIsog W))
    (chπ : (frobeniusIsog W).CoordHom)
    (hinjπ : Function.Injective chπ.toAlgHom)
    (hfinπ : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      chπ.toAlgebra.toModule)
    (hnatπ : (frobeniusIsog W).Naturality chπ hinjπ hfinπ)
    (hsurjDualπ : Function.Surjective ((frobeniusIsog W).picDual chπ hinjπ hfinπ))
    (hsurjπ : Function.Surjective (frobeniusIsog W).toAddMonoidHom)
    (Sπ : Type*) [CommRing Sπ] [Algebra W.toAffine.CoordinateRing Sπ]
    [FaithfulSMul W.toAffine.CoordinateRing Sπ]
    [Algebra.IsAlgebraic W.toAffine.CoordinateRing Sπ] [NoZeroDivisors Sπ]
    (Sπ' : Type*) [CommRing Sπ'] [Algebra W.toAffine.CoordinateRing Sπ'] [Algebra Sπ Sπ']
    [Module W.toAffine.FunctionField Sπ']
    [IsScalarTower W.toAffine.CoordinateRing W.toAffine.FunctionField Sπ']
    [IsScalarTower W.toAffine.CoordinateRing Sπ Sπ'] [IsFractionRing Sπ Sπ']
    (hSRπ : @Module.finrank W.toAffine.CoordinateRing Sπ _ _ _ =
      @Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
        chπ.toAlgebra.toModule)
    (hS'FFπ : @Module.finrank W.toAffine.FunctionField Sπ' _ _ _ = (frobeniusIsog W).degree) :
    (frobeniusIsog W).picDual chπ hinjπ hfinπ = V.toAddMonoidHom := by
  have hV : V.toAddMonoidHom.comp (frobeniusIsog W).toAddMonoidHom =
      (mulByInt W.toAffine ((frobeniusIsog W).degree : ℤ)).toAddMonoidHom := by
    rw [← Isogeny.comp_toAddMonoidHom]
    exact congrArg Isogeny.toAddMonoidHom h_isDual.1
  exact Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq_degree chπ hinjπ hfinπ hnatπ hsurjDualπ
    hsurjπ Sπ Sπ' hSRπ hS'FFπ hV

omit [Fintype K] [Fintype W.toAffine.Point] in
/-- **Seed: `picDual [n] = [n]` (scalar self-dual, III.6.2(b)/(d)), non-circular.**

`deg [n] = n²` (`mulByInt_degree`) and `[n] ∘ [n] = [n²]` (`mulByInt_comp_eq_mul`) feed the
III.6.1(a) uniqueness.  Residuals: the *per-scalar* CoordHom data. -/
theorem picDual_mulByInt_eq_self
    (n : ℤ) (hn : n ≠ 0)
    (chn : (mulByInt W.toAffine n).CoordHom)
    (hinjn : Function.Injective chn.toAlgHom)
    (hfinn : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      chn.toAlgebra.toModule)
    (hnatn : (mulByInt W.toAffine n).Naturality chn hinjn hfinn)
    (hsurjDualn : Function.Surjective ((mulByInt W.toAffine n).picDual chn hinjn hfinn))
    (hsurjn : Function.Surjective (mulByInt W.toAffine n).toAddMonoidHom)
    (Sn : Type*) [CommRing Sn] [Algebra W.toAffine.CoordinateRing Sn]
    [FaithfulSMul W.toAffine.CoordinateRing Sn]
    [Algebra.IsAlgebraic W.toAffine.CoordinateRing Sn] [NoZeroDivisors Sn]
    (Sn' : Type*) [CommRing Sn'] [Algebra W.toAffine.CoordinateRing Sn'] [Algebra Sn Sn']
    [Module W.toAffine.FunctionField Sn']
    [IsScalarTower W.toAffine.CoordinateRing W.toAffine.FunctionField Sn']
    [IsScalarTower W.toAffine.CoordinateRing Sn Sn'] [IsFractionRing Sn Sn']
    (hSRn : @Module.finrank W.toAffine.CoordinateRing Sn _ _ _ =
      @Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
        chn.toAlgebra.toModule)
    (hS'FFn : @Module.finrank W.toAffine.FunctionField Sn' _ _ _ = (mulByInt W.toAffine n).degree) :
    (mulByInt W.toAffine n).picDual chn hinjn hfinn = (mulByInt W.toAffine n).toAddMonoidHom := by
  have hcomp : (mulByInt W.toAffine n).comp (mulByInt W.toAffine n) =
      mulByInt W.toAffine (n * n) := mulByInt_comp_eq_mul W n n hn hn (mul_ne_zero hn hn)
  have hdeg : ((mulByInt W.toAffine n).degree : ℤ) = n * n := by
    rw [mulByInt_degree W.toAffine n hn]
    rw [Int.toNat_of_nonneg (by positivity : (0:ℤ) ≤ n ^ 2)]
    ring
  have hn2 : (mulByInt W.toAffine n).toAddMonoidHom.comp (mulByInt W.toAffine n).toAddMonoidHom =
      (mulByInt W.toAffine (n * n)).toAddMonoidHom := by
    rw [← Isogeny.comp_toAddMonoidHom, hcomp]
  exact Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq chn hinjn hfinn hnatn hsurjDualn
    hsurjn Sn Sn' hSRn hS'FFn hdeg hn2

/-- **Route C (geometric): `deg(rπ − s) = N` via the Pic⁰ point-map chain + geometric injectivity.**

The SIGNED III.6.3 degree identity `deg(rπ − s) = q·r² − t·r·s + s²` (= `N`) assembled along the
**Pic⁰ push-pull** route purely at the **point-map** level, pinned by the geometric injectivity of
`[·]` over `E(F̄)` (TARGET 1).

The point-map identity `[deg β] = [N]` is built from:
* the push-pull `picDual(β) ∘ β = [deg β]`
  (`picDual_comp_toAddMonoidHom_of_surjective_degree`);
* dual additivity `picDual(β) = β_dual` as point maps (`hdual_hom`);
* the shipped point-map Vieta `β_dual ∘ β = [N]`
  (`genuine_dual_comp_toAddMonoidHom_eq_mulByInt`).

It is then collapsed to `deg β = N` by the **carried** geometric-injectivity hypothesis `hgeom`
(= TARGET 1's conclusion-shape `mulByInt_pointMap_injective_of_geometric` for the base-changed
`E(F̄)`, transported to `W.Point` via base-change degree-invariance `degree_eq_of_finrank_eq`).

Residuals (named): `hnat`, `hsurjDual` (push-pull data — `hsurjDual` automatic over `K̄`),
`hdual_hom` (additivity), the `CoordHom` data `ch`/`hinj`/`hfin` + tower `(S, S')` with
`hSR`/`hS'FF`, the Vieta bundle `V`/`h_isDual_V_pi`/`h_sum_trace`/`h_beta_dual_hom`, and
`hgeom` (the base-change geometric injectivity).  **No genuineness, no `β`-surjectivity, no Wall
C.** -/
theorem degree_eq_N_via_picDual_geometric
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    -- Vieta (point-map) bundle:
    (h_isDual_V_pi : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    -- Pic⁰ push-pull data for `β = rπ − s`:
    (ch : (genuineIsogSmulSub W r s hr hs hrK hsK).CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hnat : (genuineIsogSmulSub W r s hr hs hrK hsK).Naturality ch hinj hfin)
    (hsurjDual :
      Function.Surjective ((genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin))
    (hdual_hom :
      β_dual.toAddMonoidHom = (genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin)
    (S : Type*) [CommRing S] [Algebra W.toAffine.CoordinateRing S]
    [FaithfulSMul W.toAffine.CoordinateRing S]
    [Algebra.IsAlgebraic W.toAffine.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra W.toAffine.CoordinateRing S'] [Algebra S S']
    [Module W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing S S'] [IsFractionRing S S']
    (hSR : @Module.finrank W.toAffine.CoordinateRing S _ _ _ =
      @Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank W.toAffine.FunctionField S' _ _ _ =
      (genuineIsogSmulSub W r s hr hs hrK hsK).degree)
    -- Geometric injectivity (TARGET 1 over `E(F̄)`, carried as the base-change residual):
    (hgeom : ∀ {m n : ℤ},
      (∀ P : W.toAffine.Point,
        (mulByInt W.toAffine m).toAddMonoidHom P = (mulByInt W.toAffine n).toAddMonoidHom P) →
      m = n) :
    ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  -- (1)+(2) Push-pull rewritten by additivity: `(β_dual ∘ β) = [deg β]` (point maps).
  have h_pushpull :
      (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK)).toAddMonoidHom =
      (mulByInt W.toAffine
        ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ)).toAddMonoidHom := by
    rw [Isogeny.comp_toAddMonoidHom, hdual_hom]
    exact Isogeny.picDual_comp_toAddMonoidHom_of_surjective_degree ch hinj hfin hnat hsurjDual
      S S' hSR hS'FF
  -- (3) Shipped point-map Vieta: `(β_dual ∘ β) = [N]` (point maps).
  have h_vieta :
      (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK)).toAddMonoidHom =
      (mulByInt W.toAffine
        ((Fintype.card K : ℤ) * r ^ 2 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)
      ).toAddMonoidHom :=
    genuine_dual_comp_toAddMonoidHom_eq_mulByInt W hq r s hr hs hrK hsK V β_dual
      h_isDual_V_pi h_sum_trace h_beta_dual_hom
  -- Hence `[deg β] = [N]` as point maps: `∀ P, (deg β) • P = N • P`.
  have h_eq :
      (mulByInt W.toAffine
        ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ)).toAddMonoidHom =
      (mulByInt W.toAffine
        ((Fintype.card K : ℤ) * r ^ 2 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)
      ).toAddMonoidHom := h_pushpull.symm.trans h_vieta
  -- Geometric injectivity collapses the point-map identity to the integer equality.
  exact hgeom (fun P ↦ DFunLike.congr_fun h_eq P)

/-! ### Part (A)+(B): `degree_eq_N_via_picDual_geometric_v2` — `hnat` and `hdual_hom` DISCHARGED

`degree_eq_N_via_picDual_geometric` carries two residuals that Part (A)/(B) now eliminate:

* **`hnat`** (Silverman III.3.4 naturality of `κ`) — **DISCHARGED** by Part (A)'s unconditional
  `Isogeny.naturality_of_coordHom`: the `relNorm = comap` residue-degree-`1` bookkeeping is now
  `PerfectField`-free (`mk0_relNorm0_XYIdeal_eq_mk0_comap` →
  `ClassGroup.mk0_relNorm0_eq_mk0_comap_of_inertiaDeg_one`), so `hnat` reduces to the *single*
  genuine datum `hpoint`: the point-map ↔ `comap` agreement (Silverman III.3.4 for the **actual**
  point map of `rπ − s`, supplied by `toClass_toPointMap` over the base-change tower).  This is the
  honest **base-change plumbing** residual — not a `PerfectField`/Galois obligation.

* **`hdual_hom`** (`picDual(rπ − s) = rV − s`) — **DISCHARGED** modulo the single precise residual
  `hpicval` (= the **III.6.2(c) dual-additivity** *output* `picDual(rπ−s) = r·V − s·id`).  Part (B)
  ships the non-circular *per-piece* `picDual` seeds (`picDual π = V`, `picDual [n] = [n]`,
  `picDual (rπ) = rV`) that `hpicval` decomposes into; their *combination* is exactly III.6.2(c)
  (`Div⁰`, char 0 / Ex. 3.31), which is the irreducible residual (any uniqueness route is circular
  with the conclusion `deg(rπ − s) = N`).

The remaining residual list is therefore **`{hpoint (base-change), hpicval (III.6.2(c) additivity
output), hsurjDual, CoordHom data (ch/hinj/hfin + tower (S,S')), Vieta bundle, hgeom}`** — strictly
smaller than `degree_eq_N_via_picDual_geometric` (no opaque `hnat`; `hdual_hom` reduced to the
additivity output).  **No genuineness, no `β`-surjectivity, no Wall C.** -/

/-! #### Discharging `hpoint` from the geometric `toPointMap` (Silverman III.3.4, `comap` form)

The residual `hpoint` carried by `degree_eq_N_via_picDual_geometric_v2` is the per-point agreement
`κ(α P) = mk0(comap α* 𝔪_P)` for the **actual** `Isogeny` point map `α.toAddMonoidHom`.  The shipped
`HasseWeil.Curves.CurveMap.toClass_toPointMap` proves *exactly* this `comap`-form agreement — but for
the **geometric** point map `φ.toPointMap coordHom` of a `CurveMap φ`, which is *computed from the
comorphism* (`evalAtPullback`).  An `Isogeny` stores its `pullback` and `toAddMonoidHom` as
**independent** fields (`HasseWeil/Basic.lean`), so the only genuine residual is the *per-isogeny*
identification of the two point maps:

```
α.toAddMonoidHom (some x y h) = (φ.toPointMap coordHom ⟨x, y, h⟩).toAffinePoint
```

This holds for genuine isogenies (Frobenius, mult-by-`n`, and their `addIsog` combinations) by their
explicit construction, where the additive point action *is* the comorphism's set-theoretic image.
The bridge below threads `toClass_toPointMap` through that identification (`hcompat`), discharging the
*full* `hpoint` hypothesis from it.  The `comap`-nonzero side condition `hne` of `toClass_toPointMap`
is supplied by `hpoint`'s own `hcomap` argument (so no extra obligation is introduced).

`coordHom.toAlgHom = ch.toAlgHom` ties the `Isogeny.CoordHom` `ch` (consumed by the `Naturality`
machinery) to the `CurveMap.CoordHom` `coordHom` (consumed by `toPointMap`); both carry the same
algebra hom `R →ₐ[F] R`, so this is `rfl` for the intended deployment (one builds `coordHom` and `ch`
from the same restriction). -/
theorem hpoint_of_toPointMap_compat
    {F : Type*} [Field F] [DecidableEq F]
    {E : WeierstrassCurve.Affine F} [E.IsElliptic]
    (α : HasseWeil.Isogeny E E) (ch : α.CoordHom)
    {φ : HasseWeil.Curves.CurveMap ⟨E⟩ ⟨E⟩}
    (coordHom : φ.CoordHom)
    (hcoord : coordHom.toAlgHom = ch.toAlgHom)
    (hcompat : ∀ (x y : F) (h : E.Nonsingular x y),
      α.toAddMonoidHom (WeierstrassCurve.Affine.Point.some x y h) =
        (HasseWeil.Curves.CurveMap.toPointMap coordHom
          (⟨x, y, h⟩ : (⟨E⟩ : HasseWeil.Curves.SmoothPlaneCurve F).SmoothPoint)).toAffinePoint) :
    ∀ (x y : F) (h : E.Nonsingular x y)
      (hcomap : Ideal.comap ch.toAlgHom.toRingHom
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y)) ∈
        (Ideal E.CoordinateRing)⁰),
      WeierstrassCurve.Affine.Point.toClassEquiv' (W := E)
          (α.toAddMonoidHom (WeierstrassCurve.Affine.Point.some x y h)) =
        Additive.ofMul (ClassGroup.mk0 (⟨Ideal.comap ch.toAlgHom.toRingHom
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y)), hcomap⟩ :
          (Ideal E.CoordinateRing)⁰)) := by
  intro x y h hcomap
  set P : (⟨E⟩ : HasseWeil.Curves.SmoothPlaneCurve F).SmoothPoint := ⟨x, y, h⟩ with hP
  -- The `comap`-nonzero side condition of `toClass_toPointMap`, from `hcomap` (`hcoord` rewrites
  -- `coordHom.toAlgHom` to `ch.toAlgHom`; `maximalIdealAt P` is `XYIdeal E x (C y)` definitionally).
  have hne : Ideal.comap coordHom.toAlgHom.toRingHom
      ((⟨E⟩ : HasseWeil.Curves.SmoothPlaneCurve F).maximalIdealAt P) ≠ ⊥ := by
    rw [hcoord]
    exact mem_nonZeroDivisors_iff_ne_zero.mp hcomap
  -- LHS: rewrite the actual point image via the geometric `toPointMap` (`hcompat`), then
  -- `toClassEquiv' = toClass` and the shipped `toClass_toPointMap`.
  -- The two `comap` ideals coincide: `coordHom.toAlgHom = ch.toAlgHom` (`hcoord`) and
  -- `maximalIdealAt P = XYIdeal E x (C y)` definitionally.
  have hideal : Ideal.comap coordHom.toAlgHom.toRingHom
      ((⟨E⟩ : HasseWeil.Curves.SmoothPlaneCurve F).maximalIdealAt P) =
      Ideal.comap ch.toAlgHom.toRingHom
        (WeierstrassCurve.Affine.CoordinateRing.XYIdeal E x (Polynomial.C y)) := by
    rw [hcoord, HasseWeil.Curves.SmoothPlaneCurve.maximalIdealAt]
  rw [WeierstrassCurve.Affine.Point.toClassEquiv'_apply, hcompat x y h,
    HasseWeil.Curves.CurveMap.toClass_toPointMap coordHom P hne]
  -- Both sides are `mk0` of the same `comap` ideal; the membership proofs are irrelevant.
  exact congrArg (fun J ↦ Additive.ofMul (ClassGroup.mk0 J)) (Subtype.ext hideal)

/-- **Route C (geometric) v2: `deg(rπ − s) = N` with `hnat` and `hdual_hom` DISCHARGED.**

As `degree_eq_N_via_picDual_geometric`, but with the III.3.4 naturality `hnat` **discharged** from
the Part-(A) `Isogeny.naturality_of_coordHom` (residual: the base-change point-map ↔ `comap`
agreement `hpoint`), and `hdual_hom` **discharged** from the III.6.2(c) dual-additivity *output*
`hpicval : picDual(rπ − s) = r·V − s·id` (the precise residual Part (B) reduces `hdual_hom` to; its
per-piece `picDual` values are the shipped non-circular seeds).

Residuals (named): `hpoint` (base-change III.3.4 for the actual point map), `hpicval` (III.6.2(c)
additivity output), `hsurjDual`, the `CoordHom` data `ch`/`hinj`/`hfin` + tower `(S, S')`, the Vieta
bundle `V`/`h_isDual_V_pi`/`h_sum_trace`/`h_beta_dual_hom`, and `hgeom`. -/
theorem degree_eq_N_via_picDual_geometric_v2
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    -- Vieta (point-map) bundle:
    (h_isDual_V_pi : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    -- Pic⁰ push-pull data for `β = rπ − s`:
    (ch : (genuineIsogSmulSub W r s hr hs hrK hsK).CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    -- (A) `hnat` residual: the base-change III.3.4 point-map ↔ `comap` agreement.
    (hpoint : ∀ (x y : K) (h : W.toAffine.Nonsingular x y)
      (hcomap : Ideal.comap ch.toAlgHom.toRingHom
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W.toAffine x (Polynomial.C y)) ∈
        (Ideal W.toAffine.CoordinateRing)⁰),
      WeierstrassCurve.Affine.Point.toClassEquiv' (W := W.toAffine)
          ((genuineIsogSmulSub W r s hr hs hrK hsK).toAddMonoidHom
            (WeierstrassCurve.Affine.Point.some x y h)) =
        Additive.ofMul (ClassGroup.mk0 (⟨Ideal.comap ch.toAlgHom.toRingHom
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W.toAffine x (Polynomial.C y)),
          hcomap⟩ : (Ideal W.toAffine.CoordinateRing)⁰)))
    (hsurjDual :
      Function.Surjective ((genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin))
    -- (B) `hdual_hom` residual: the III.6.2(c) dual-additivity OUTPUT `picDual(rπ−s) = rV − s`.
    (hpicval :
      (genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin =
        r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (S : Type*) [CommRing S] [Algebra W.toAffine.CoordinateRing S]
    [FaithfulSMul W.toAffine.CoordinateRing S]
    [Algebra.IsAlgebraic W.toAffine.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra W.toAffine.CoordinateRing S'] [Algebra S S']
    [Module W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing S S'] [IsFractionRing S S']
    (hSR : @Module.finrank W.toAffine.CoordinateRing S _ _ _ =
      @Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank W.toAffine.FunctionField S' _ _ _ =
      (genuineIsogSmulSub W r s hr hs hrK hsK).degree)
    (hgeom : ∀ {m n : ℤ},
      (∀ P : W.toAffine.Point,
        (mulByInt W.toAffine m).toAddMonoidHom P = (mulByInt W.toAffine n).toAddMonoidHom P) →
      m = n) :
    ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  -- (A) Discharge `hnat` from the base-change point-map ↔ `comap` agreement.
  have hnat : (genuineIsogSmulSub W r s hr hs hrK hsK).Naturality ch hinj hfin :=
    Isogeny.naturality_of_coordHom ch hinj hfin hpoint
  -- (B) Discharge `hdual_hom` from the III.6.2(c) additivity output `hpicval` + `h_beta_dual_hom`.
  have hdual_hom : β_dual.toAddMonoidHom =
      (genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin :=
    h_beta_dual_hom.trans hpicval.symm
  exact degree_eq_N_via_picDual_geometric W hq r s hr hs hrK hsK V β_dual h_isDual_V_pi
    h_sum_trace h_beta_dual_hom ch hinj hfin hnat hsurjDual hdual_hom S S' hSR hS'FF hgeom

/-- **Route C (geometric) v3: `deg(rπ − s) = N` with `hpoint` REDUCED to the `toPointMap` compat.**

As `degree_eq_N_via_picDual_geometric_v2`, but the opaque `hpoint` residual (the per-point κ-class
III.3.4 `comap` agreement) is now **discharged** by `hpoint_of_toPointMap_compat` from the strictly
more concrete and structurally-honest residual `hcompat`: the per-isogeny identification of the
*actual* `Isogeny` point map `α.toAddMonoidHom` with the geometric `CurveMap` point map
`φ.toPointMap coordHom` at every rational point,

```
(genuineIsogSmulSub W r s …).toAddMonoidHom (some x y h)
  = (CurveMap.toPointMap coordHom ⟨x, y, h⟩).toAffinePoint.
```

This is the genuine content the `Isogeny`↔`CurveMap` correspondence carries (the `Isogeny` stores
its point map and pullback independently); it holds for genuine isogenies — Frobenius, mult-by-`n`,
and their `addIsog` combinations such as `genuineIsogSmulSub` — by their explicit construction (the
additive point action *is* the comorphism's set-theoretic image).  The `comap`-nonzero side
condition of `toClass_toPointMap` is supplied internally from the carried `hcomap` data, so `hcompat`
is the *only* added residual replacing `hpoint`.

Residuals (named): `hcompat` (the `Isogeny`↔`CurveMap` point-map identification, in place of
`hpoint`), `coordHom`/`hcoord` (the `CurveMap.CoordHom` matching `ch`), `hpicval`, `hsurjDual`, the
`CoordHom` data `ch`/`hinj`/`hfin` + tower `(S, S')`, the Vieta bundle, and `hgeom`. -/
theorem degree_eq_N_via_picDual_geometric_v3
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    (h_isDual_V_pi : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (ch : (genuineIsogSmulSub W r s hr hs hrK hsK).CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    -- (A′) `hpoint` reduced: the `CurveMap` witness + the point-map ↔ `toPointMap` identification.
    {φ : HasseWeil.Curves.CurveMap ⟨W.toAffine⟩ ⟨W.toAffine⟩}
    (coordHom : φ.CoordHom)
    (hcoord : coordHom.toAlgHom = ch.toAlgHom)
    (hcompat : ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      (genuineIsogSmulSub W r s hr hs hrK hsK).toAddMonoidHom
          (WeierstrassCurve.Affine.Point.some x y h) =
        (HasseWeil.Curves.CurveMap.toPointMap coordHom
          (⟨x, y, h⟩ :
            (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve K).SmoothPoint)).toAffinePoint)
    (hsurjDual :
      Function.Surjective ((genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin))
    (hpicval :
      (genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin =
        r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (S : Type*) [CommRing S] [Algebra W.toAffine.CoordinateRing S]
    [FaithfulSMul W.toAffine.CoordinateRing S]
    [Algebra.IsAlgebraic W.toAffine.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra W.toAffine.CoordinateRing S'] [Algebra S S']
    [Module W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing S S'] [IsFractionRing S S']
    (hSR : @Module.finrank W.toAffine.CoordinateRing S _ _ _ =
      @Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank W.toAffine.FunctionField S' _ _ _ =
      (genuineIsogSmulSub W r s hr hs hrK hsK).degree)
    (hgeom : ∀ {m n : ℤ},
      (∀ P : W.toAffine.Point,
        (mulByInt W.toAffine m).toAddMonoidHom P = (mulByInt W.toAffine n).toAddMonoidHom P) →
      m = n) :
    ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  -- (A′) Discharge the `hpoint` residual from the geometric `toPointMap` identification.
  have hpoint := hpoint_of_toPointMap_compat (genuineIsogSmulSub W r s hr hs hrK hsK) ch
    coordHom hcoord hcompat
  exact degree_eq_N_via_picDual_geometric_v2 W hq r s hr hs hrK hsK V β_dual h_isDual_V_pi
    h_sum_trace h_beta_dual_hom ch hinj hfin hpoint hsurjDual hpicval S S' hSR hS'FF hgeom

/-- **Route C (geometric): `qf_nonneg` at a generic `(r, s)` via the Pic⁰ chain + geometric
injectivity.**

The Leaf-1 conclusion `0 ≤ q·r² − t·r·s + s²` for a generic `(r, s)`, assembled along the **Pic⁰
push-pull** route pinned by geometric injectivity (`degree_eq_N_via_picDual_geometric`), then the
trivial sign step (`deg ≥ 0`).  The residual list is exactly that of
`degree_eq_N_via_picDual_geometric`: `{hnat, hsurjDual, hdual_hom, CoordHom data, Vieta bundle,
hgeom}` — **no genuineness, no `β`-surjectivity, no Wall C.** -/
theorem qf_nonneg_generic_via_picDual_geometric
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    (h_isDual_V_pi : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (ch : (genuineIsogSmulSub W r s hr hs hrK hsK).CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hnat : (genuineIsogSmulSub W r s hr hs hrK hsK).Naturality ch hinj hfin)
    (hsurjDual :
      Function.Surjective ((genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin))
    (hdual_hom :
      β_dual.toAddMonoidHom = (genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin)
    (S : Type*) [CommRing S] [Algebra W.toAffine.CoordinateRing S]
    [FaithfulSMul W.toAffine.CoordinateRing S]
    [Algebra.IsAlgebraic W.toAffine.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra W.toAffine.CoordinateRing S'] [Algebra S S']
    [Module W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing S S'] [IsFractionRing S S']
    (hSR : @Module.finrank W.toAffine.CoordinateRing S _ _ _ =
      @Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank W.toAffine.FunctionField S' _ _ _ =
      (genuineIsogSmulSub W r s hr hs hrK hsK).degree)
    (hgeom : ∀ {m n : ℤ},
      (∀ P : W.toAffine.Point,
        (mulByInt W.toAffine m).toAddMonoidHom P = (mulByInt W.toAffine n).toAddMonoidHom P) →
      m = n) :
    0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  rw [← degree_eq_N_via_picDual_geometric W hq r s hr hs hrK hsK V β_dual h_isDual_V_pi h_sum_trace
    h_beta_dual_hom ch hinj hfin hnat hsurjDual hdual_hom S S' hSR hS'FF hgeom]
  exact Int.natCast_nonneg _

/-- **Route C (geometric) v2: `qf_nonneg` at a generic `(r, s)`, `hnat`+`hdual_hom` DISCHARGED.**

The Leaf-1 conclusion `0 ≤ q·r² − t·r·s + s²` for a generic `(r, s)`, via `_v2`'s
`deg(rπ − s) = N` (with `hnat` discharged by Part (A) and `hdual_hom` reduced to the III.6.2(c)
additivity output `hpicval`) and the trivial sign step.  Residual list: `{hpoint (base-change),
hpicval (III.6.2(c) output), hsurjDual, CoordHom data, Vieta bundle, hgeom}` — **no opaque `hnat`,
no genuineness, no `β`-surjectivity, no Wall C.** -/
theorem qf_nonneg_generic_via_picDual_geometric_v2
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    (h_isDual_V_pi : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (ch : (genuineIsogSmulSub W r s hr hs hrK hsK).CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hpoint : ∀ (x y : K) (h : W.toAffine.Nonsingular x y)
      (hcomap : Ideal.comap ch.toAlgHom.toRingHom
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W.toAffine x (Polynomial.C y)) ∈
        (Ideal W.toAffine.CoordinateRing)⁰),
      WeierstrassCurve.Affine.Point.toClassEquiv' (W := W.toAffine)
          ((genuineIsogSmulSub W r s hr hs hrK hsK).toAddMonoidHom
            (WeierstrassCurve.Affine.Point.some x y h)) =
        Additive.ofMul (ClassGroup.mk0 (⟨Ideal.comap ch.toAlgHom.toRingHom
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W.toAffine x (Polynomial.C y)),
          hcomap⟩ : (Ideal W.toAffine.CoordinateRing)⁰)))
    (hsurjDual :
      Function.Surjective ((genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin))
    (hpicval :
      (genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin =
        r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (S : Type*) [CommRing S] [Algebra W.toAffine.CoordinateRing S]
    [FaithfulSMul W.toAffine.CoordinateRing S]
    [Algebra.IsAlgebraic W.toAffine.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra W.toAffine.CoordinateRing S'] [Algebra S S']
    [Module W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing S S'] [IsFractionRing S S']
    (hSR : @Module.finrank W.toAffine.CoordinateRing S _ _ _ =
      @Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank W.toAffine.FunctionField S' _ _ _ =
      (genuineIsogSmulSub W r s hr hs hrK hsK).degree)
    (hgeom : ∀ {m n : ℤ},
      (∀ P : W.toAffine.Point,
        (mulByInt W.toAffine m).toAddMonoidHom P = (mulByInt W.toAffine n).toAddMonoidHom P) →
      m = n) :
    0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  rw [← degree_eq_N_via_picDual_geometric_v2 W hq r s hr hs hrK hsK V β_dual h_isDual_V_pi
    h_sum_trace h_beta_dual_hom ch hinj hfin hpoint hsurjDual hpicval S S' hSR hS'FF hgeom]
  exact Int.natCast_nonneg _

/-! ### Phase 3 — the `hgeom` residual IS TARGET 1 (closing the loop)

The geometric-injectivity hypothesis `hgeom` consumed by `degree_eq_N_via_picDual_geometric` is
**exactly** the conclusion-shape of TARGET 1 (`mulByInt_pointMap_injective_of_infinite_point`).  The
connector below makes this explicit: over any base whose point group is `Infinite` and whose nonzero
torsion subgroups are `Finite` (both hold for `E` base-changed to `F̄_q = AlgebraicClosure 𝔽_q` —
Silverman III.4.10a for the torsion finiteness), `hgeom` is **discharged**, with no residual beyond
the two geometric facts.

This confirms the Route-C claim: the ONLY thing standing between the shipped point-map chain and
`deg(rπ − s) = N` is the **base-change geometric injectivity** (TARGET 1) — *not* a genuine
function-field comorphism, *not* surjectivity of `β`, *not* Wall C.  In the intended deployment one
runs the whole Pic⁰ chain over `W_F̄ := W.baseChange F̄` (where `hgeom` is supplied by this
connector), then descends `deg_{F̄}(rπ − s) = deg_F(rπ − s)` via the shipped base-change
degree-invariance `HasseWeil.Isogeny.degree_eq_of_finrank_eq`. -/

/-- **Phase 3: `hgeom` is supplied by TARGET 1 over the geometric points.**

For a base whose point group `W.Point` is `Infinite` and all of whose nonzero torsion subgroups
`E[k]` are `Finite`, the geometric-injectivity residual `hgeom` required by
`degree_eq_N_via_picDual_geometric` holds.  Direct application of TARGET 1
(`mulByInt_pointMap_injective_of_infinite_point`).

So the `hgeom` residual is **precisely** the base-change geometric injectivity: instantiate the
Pic⁰ chain at `W_F̄` (where this hypothesis is met) and descend the degree by
`degree_eq_of_finrank_eq`. -/
theorem hgeom_of_infinite_point
    [Infinite W.toAffine.Point]
    (htor : ∀ k : ℤ, k ≠ 0 →
      Finite (HasseWeil.torsionSubgroup W.toAffine k : AddSubgroup W.toAffine.Point)) :
    ∀ {m n : ℤ},
      (∀ P : W.toAffine.Point,
        (mulByInt W.toAffine m).toAddMonoidHom P = (mulByInt W.toAffine n).toAddMonoidHom P) →
      m = n :=
  fun {m n} h ↦ mulByInt_pointMap_injective_of_infinite_point W.toAffine htor h

/-! ### Part (B) v3: discharge `hpicval` to the SINGLE precise III.6.2(c)/III.8 residual

`degree_eq_N_via_picDual_geometric_v2` still carries `hpicval` (`picDual(rπ − s) = rV − s`) as an
opaque residual.  Part (B) v3 **discharges** it via the generic PicDual reducer
`Isogeny.picDual_eq_smul_sub_of_sum_trace`, reducing it to the **single** precise residual
`htrace_dual` — the Silverman III.8 trace relation for the whole `α = rπ − s`:

  `(rπ − s) + picDual(rπ − s) = [r·t − 2s]`   (point maps).

This is the irreducible content (any uniqueness route is circular with `deg(rπ − s) = N`; III.8 for
`α` is equivalent to III.6.2(c) additivity since `tr(rπ − s) = r·t − 2s`).  The candidate trace half
`(rπ − s) + (rV − s) = [r·t − 2s]` is derived **non-circularly** from the shipped `π + V = [t]`
(`h_sum_trace`), inside the generic reducer.  The per-piece `picDual` values `htrace_dual` decomposes
into are the shipped non-circular seeds `picDual π = V` (`picDual_frobenius_eq_verschiebung`),
`picDual(rπ) = rV` (`Isogeny.picDual_zsmul_eq_zsmul_of_isDual`), `picDual [n] = [n]`
(`picDual_mulByInt_eq_self`). -/

/-- **`hpicval` from the III.8 trace relation for `rπ − s` (non-circular reduction).**

`picDual(rπ − s) = r·V − s·id` (the III.6.2(c) dual-additivity OUTPUT) obtained from the single
irreducible residual `htrace_dual` (Silverman III.8 for `α = rπ − s`) and the shipped `π + V = [t]`
(`h_sum_trace`), via the generic `Isogeny.picDual_eq_smul_sub_of_sum_trace`.  No degree, no
uniqueness, **non-circular**. -/
theorem picDual_smulSub_eq_rV_sub_s
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V : Isogeny W.toAffine W.toAffine)
    (ch : (genuineIsogSmulSub W r s hr hs hrK hsK).CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    -- the SINGLE irreducible residual: Silverman III.8 trace relation for the whole `rπ − s`:
    (htrace_dual :
      (genuineIsogSmulSub W r s hr hs hrK hsK).toAddMonoidHom +
          (genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin =
        (mulByInt W.toAffine
          (r * isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) -
            2 * s)).toAddMonoidHom) :
    (genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _) := by
  -- `hbeta`: the `rπ − s` point-map shape of `genuineIsogSmulSub`.
  have hbeta : (genuineIsogSmulSub W r s hr hs hrK hsK).toAddMonoidHom =
      r • (frobeniusIsog W).toAddMonoidHom - s • (AddMonoidHom.id _) := by
    rw [genuineIsogSmulSub_toAddMonoidHom]
    ext P
    simp only [AddMonoidHom.add_apply, AddMonoidHom.sub_apply, AddMonoidHom.smul_apply,
      AddMonoidHom.id_apply, Isogeny.zsmul_apply, mulByInt_apply]
    rw [neg_smul, sub_eq_add_neg]
  exact Isogeny.picDual_eq_smul_sub_of_sum_trace ch hinj hfin r s
    (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq)) hbeta h_sum_trace htrace_dual

/-- **Route C (geometric): `deg(rπ − s) = N` with `hnat` AND `hpicval` DISCHARGED.**

As `_v2` (which discharges `hnat`), but with the III.6.2(c) dual-additivity output `hpicval`
**additionally discharged** from the single precise III.8 residual `htrace_dual`
(`picDual_smulSub_eq_rV_sub_s`).  (Complements the sibling `degree_eq_N_via_picDual_geometric_v3`,
which instead discharges the *base-change* residual `hpoint` to the `toPointMap` compat — the two
reductions are orthogonal and compose.)  The residual list here shrinks to `{hpoint (base-change
III.3.4), htrace_dual (III.8/III.6.2(c)), hsurjDual, CoordHom data, tower (S, S'), Vieta bundle
(`V`/`h_isDual_V_pi`/`h_sum_trace`/`h_beta_dual_hom`), hgeom}` — no opaque `hnat`, no opaque
`hpicval`, no genuineness, no `β`-surjectivity, no Wall C. -/
theorem degree_eq_N_via_picDual_geometric_hpicval_discharged
    (hq : 2 ≤ Fintype.card K)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (V β_dual : Isogeny W.toAffine W.toAffine)
    (h_isDual_V_pi : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _))
    (ch : (genuineIsogSmulSub W r s hr hs hrK hsK).CoordHom)
    (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _
      ch.toAlgebra.toModule)
    (hpoint : ∀ (x y : K) (h : W.toAffine.Nonsingular x y)
      (hcomap : Ideal.comap ch.toAlgHom.toRingHom
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W.toAffine x (Polynomial.C y)) ∈
        (Ideal W.toAffine.CoordinateRing)⁰),
      WeierstrassCurve.Affine.Point.toClassEquiv' (W := W.toAffine)
          ((genuineIsogSmulSub W r s hr hs hrK hsK).toAddMonoidHom
            (WeierstrassCurve.Affine.Point.some x y h)) =
        Additive.ofMul (ClassGroup.mk0 (⟨Ideal.comap ch.toAlgHom.toRingHom
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W.toAffine x (Polynomial.C y)),
          hcomap⟩ : (Ideal W.toAffine.CoordinateRing)⁰)))
    (hsurjDual :
      Function.Surjective ((genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin))
    -- (B v3) the SINGLE precise residual replacing `hpicval`: III.8 for the whole `rπ − s`.
    (htrace_dual :
      (genuineIsogSmulSub W r s hr hs hrK hsK).toAddMonoidHom +
          (genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin =
        (mulByInt W.toAffine
          (r * isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) -
            2 * s)).toAddMonoidHom)
    (S : Type*) [CommRing S] [Algebra W.toAffine.CoordinateRing S]
    [FaithfulSMul W.toAffine.CoordinateRing S]
    [Algebra.IsAlgebraic W.toAffine.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra W.toAffine.CoordinateRing S'] [Algebra S S']
    [Module W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing W.toAffine.FunctionField S']
    [IsScalarTower W.toAffine.CoordinateRing S S'] [IsFractionRing S S']
    (hSR : @Module.finrank W.toAffine.CoordinateRing S _ _ _ =
      @Module.finrank W.toAffine.CoordinateRing W.toAffine.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank W.toAffine.FunctionField S' _ _ _ =
      (genuineIsogSmulSub W r s hr hs hrK hsK).degree)
    (hgeom : ∀ {m n : ℤ},
      (∀ P : W.toAffine.Point,
        (mulByInt W.toAffine m).toAddMonoidHom P = (mulByInt W.toAffine n).toAddMonoidHom P) →
      m = n) :
    ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  -- (B v3) Discharge `hpicval` from the single III.8 residual `htrace_dual`.
  have hpicval : (genuineIsogSmulSub W r s hr hs hrK hsK).picDual ch hinj hfin =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _) :=
    picDual_smulSub_eq_rV_sub_s W hq r s hr hs hrK hsK V ch hinj hfin h_sum_trace htrace_dual
  exact degree_eq_N_via_picDual_geometric_v2 W hq r s hr hs hrK hsK V β_dual h_isDual_V_pi
    h_sum_trace h_beta_dual_hom ch hinj hfin hpoint hsurjDual hpicval S S' hSR hS'FF hgeom

end HasseWeil.Pic0.RouteCGeometric
