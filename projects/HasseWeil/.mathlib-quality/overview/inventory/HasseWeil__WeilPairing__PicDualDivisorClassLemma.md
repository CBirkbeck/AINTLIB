# Inventory: ./HasseWeil/WeilPairing/PicDualDivisorClassLemma.lean

**File purpose**: Discharge the projective-divisor-class identity `PicDualDivisorClass φ` (Silverman
III.6.1b `φ^*((T) − (O)) ∼ (φ̂ T) − (O)`) via the **Abel–Jacobi σ-machinery**, turning the separable
Weil-pairing adjoint into an unconditional consequence of the standard per-isogeny data. Two layers:
(1) the **primitive σ/degree facts** about `pullbackDivisor φ ((T) − (O))` (degree 0, σ = #ker·P₀) —
these are field-agnostic and **LIVE**; (2) a **picDual-based discharge chain** (`PicDualDivisorClass`
from `φ̂ ∘ φ = [#ker φ]`, then from III.3.4 naturality, then the `[ℓ]` instance, then the adjoint) — this
entire chain is **DEAD/SUPERSEDED** by the CoordHom-free `δ`-based mirrors in `SeparableScaling.lean`.

> **⚠️ Why the picDual chain is dead.** It is parameterized by a `φ.CoordHom` (`ch`/`hinj`/`hfin`) and
> `picDual φ ch …`. Per the project's verified impossibility (`mulByInt CoordHom IMPOSSIBLE`,
> `MEMORY.md`), `(mulByInt ℓ).CoordHom` does **not** exist, so this chain can never be instantiated for
> `φ = [ℓ]`. `SeparableScaling.lean` replaces `picDual φ` by an **abstract dual point map `δ`** with
> `δ ∘ φ = [#ker φ]` (no CoordHom, no surjectivity) and re-proves the same results — those are the live
> ones used by the capstone.

**Imports**: `HasseWeil.WeilPairing.HfactLemma`

**Total declarations**: 8 top-level `theorem`. **LIVE ratio: 3/8.** (Matches the audit.)

**Options set**: `linter.unusedSectionVars false`, `linter.unusedDecidableInType false`,
`linter.style.longLine false`.

**Variables**: `{F} [Field F] [DecidableEq F]`, `(W : WeierstrassCurve F) [IsElliptic]`,
`[IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]`; the last two theorems add
`[IsAlgClosed F]`.

---

## LIVE declarations (the primitive σ/degree facts)

### `theorem pullbackDivisor_kappaDivisor_eq`  — **LIVE**
- **Type**: `(f : W.toAffine.Point →+ W.toAffine.Point) (hf : Finite f.ker) (T) : pullbackDivisor f hf (kappaDivisor T) = pullbackDiv f hf T − pullbackDiv f hf 0`
- **What**: the fibre-pullback of `kappaDivisor T = (T) − (O)` is the multiplicity-free fibre difference
  `φ^*(T) − φ^*(O)`. General-`φ` analogue of `HfactLemma.pullbackDivisor_kappaDivisor` (stated for `[ℓ]`).
- **How**: `kappaDivisor`, `← pullbackDivisorHom_apply`, `map_sub`, `pullbackDivisor_single` (twice),
  `one_smul`, `toProjectiveSmoothPoint_toAffinePoint`, `toAffinePoint_infinity`.
- **Hypotheses**: `Finite f.ker`.
- **Uses from project**: `pullbackDivisor(Hom_apply)`, `pullbackDiv`, `Curves.kappaDivisor`,
  `pullbackDivisor_single`, `Affine.Point.toProjectiveSmoothPoint_toAffinePoint`,
  `ProjectiveSmoothPoint.toAffinePoint_infinity`.
- **Used by**: `degree_pullbackDivisor_kappaDivisor` (L109), `sigma_pullbackDivisor_kappaDivisor` (L123) —
  both this file (no external consumer, but its two consumers are externally live).
- **Visibility**: public. **Lines**: 88–95, ~3 lines. **LIVE (transitively).**

---

### `theorem degree_pullbackDivisor_kappaDivisor`  — **LIVE**
- **Type**: `(f) (hf) {T P₀} (hP₀ : f P₀ = T) : (pullbackDivisor f hf (kappaDivisor T)).degree = 0`
- **What**: `deg(φ^*((T) − (O))) = 0` (both fibre summands have degree `#ker φ`).
- **How**: `pullbackDivisor_kappaDivisor_eq`, `← degreeHom_apply`, `map_sub`, `degreeHom_apply` (twice),
  `degree_pullbackDiv` (at `hP₀` and `map_zero f`), `sub_self`.
- **Hypotheses**: a preimage `hP₀`.
- **Uses from project**: `pullbackDivisor_kappaDivisor_eq` (this file), `ProjectiveDivisor.degreeHom(_apply)`,
  `degree_pullbackDiv` (the per-fibre degree fact), `kappaDivisor`.
- **Used by**: `picDualDivisorClass_of_picDualComp` (L188, but that is dead) **and externally —
  the live use** `SeparableScaling.lean:144,173,523` (real `rw` uses).
- **Visibility**: public. **Lines**: 105–112, ~4 lines. **LIVE.**

---

### `theorem sigma_pullbackDivisor_kappaDivisor`  — **LIVE**
- **Type**: `(f) (hf) {T P₀} (hP₀ : f P₀ = T) : projectiveDivisorSum W.toAffine (pullbackDivisor f hf (kappaDivisor T)) = Nat.card f.ker • P₀`
- **What**: **the σ-point-identity geometric half** (Silverman III.6.1b σ-bridge): `σ = #ker(φ) · P₀`.
- **How**: `pullbackDivisor_kappaDivisor_eq`, `projectiveDivisorSum_sub`, `sigma_pullbackDiv_sub`
  (the SigmaBridge primitive).
- **Hypotheses**: a preimage `hP₀`.
- **Uses from project**: `pullbackDivisor_kappaDivisor_eq` (this file), `projectiveDivisorSum(_sub)`,
  `sigma_pullbackDiv_sub` (`SigmaBridge.lean`), `kappaDivisor`.
- **Used by**: `sigma_pullbackDivisor_kappaDivisor_eq_picDual` (L147, dead) **and externally — the live
  uses** `SeparableScaling.lean:111,527` and `OneSubDualDivisor.lean:296` (real uses).
- **Visibility**: public. **Lines**: 117–124, ~2 lines. **LIVE.** **Key API.**

---

## DEAD/SUPERSEDED declarations (the picDual + CoordHom chain)

> All five below are superseded by CoordHom-free `δ`-based mirrors in `SeparableScaling.lean`. None has a
> real (non-comment) consumer anywhere in the project. The capstone reaches the separable adjoint and
> scaling through the `SeparableScaling` mirrors instead. **Safe to delete** (subject to confirming the
> docstring cross-references in `SeparableScaling.lean` are updated — they currently *cite* these as the
> "mirror originals").

### `theorem sigma_pullbackDivisor_kappaDivisor_eq_picDual`  — **DEAD/SUPERSEDED**
- **Type**: takes `φ : Isogeny`, `ch : φ.CoordHom`, `hinj`, `hfin`, `hpdc : (φ.picDual …).comp φ = [#ker]`,
  `{T P₀} (hP₀)`; concludes `projectiveDivisorSum (pullbackDivisor φ.toAddMonoidHom … (kappaDivisor T)) = (φ.picDual …) T`.
- **What**: the full σ-point-identity `σ = φ̂ T` from the dual relation, in terms of `picDual φ`.
- **How**: `sigma_pullbackDivisor_kappaDivisor` + `hpdc` at `P₀` (`AddMonoidHom.comp_apply`, `hP₀`,
  `mulByInt_apply`, `natCast_zsmul`).
- **Uses from project**: `sigma_pullbackDivisor_kappaDivisor` (this file), `Isogeny.picDual`, `mulByInt(_apply)`,
  `pullbackDivisor`, `kappaDivisor`.
- **Used by**: `picDualDivisorClass_of_picDualComp` (L192, itself dead). **No live consumer.**
- **Visibility**: public. **Lines**: 135–151, ~5 lines.
- **DEAD.** Mirror: `SeparableScaling.sigma_pullbackDivisor_kappaDivisor_eq_dual` (L101, `δ` not `picDual`).

### `theorem picDualDivisorClass_of_picDualComp`  — **DEAD/SUPERSEDED**
- **Type**: `φ`, `ch`/`hinj`/`hfin`, `hpdc : φ̂ ∘ φ = [#ker]`, `hsurj : Surjective φ`; concludes
  `PicDualDivisorClass W φ ch hinj hfin`.
- **What**: `PicDualDivisorClass φ` from the dual relation + point-surjectivity, via Abel.
- **How**: for each `T`, preimage `P₀` (`hsurj`); `projIsPrincipal_of_degZero_of_sigma_eq_zero` with degree-0
  (`degree_pullbackDivisor_kappaDivisor`, `kappaDivisor_degree`) and `σ = 0`
  (`sigma_pullbackDivisor_kappaDivisor_eq_picDual`, `projectiveDivisorSum_kappaDivisor`).
- **Uses from project**: `PicDualDivisorClass`, `projIsPrincipal_of_degZero_of_sigma_eq_zero`,
  `degree_pullbackDivisor_kappaDivisor`/`sigma_pullbackDivisor_kappaDivisor_eq_picDual` (this file),
  `Curves.kappaDivisor_degree`, `projectiveDivisorSum_sub/_kappaDivisor`, `Isogeny.picDual`.
- **Used by**: `picDualDivisorClass_of_naturality` (L226, dead). **No live consumer.**
- **Visibility**: public. **Lines**: 173–193, ~13 lines.
- **DEAD.** Mirror: `SeparableScaling.pullbackDivisorClass_of_dualComp` (L129).

### `theorem picDualDivisorClass_of_naturality`  — **DEAD/SUPERSEDED**
- **Type**: `φ`, `ch`/`hinj`/`hfin`, `hnat : φ.Naturality`, `hsurjDual`, `hsurj`, `hcard : #ker φ = finrank R R`;
  concludes `PicDualDivisorClass W φ ch hinj hfin`.
- **What**: `PicDualDivisorClass φ` from the standard III.3.4/III.6.2(a) witnesses (the dual relation is the
  shipped `picDual_comp_toAddMonoidHom_of_surjective`).
- **How**: `picDualDivisorClass_of_picDualComp`; the dual relation via
  `Isogeny.picDual_comp_toAddMonoidHom_of_surjective` rewritten through `hcard`.
- **Uses from project**: `picDualDivisorClass_of_picDualComp` (this file),
  `Isogeny.picDual_comp_toAddMonoidHom_of_surjective`, `Naturality`, `Module.finrank`.
- **Used by**: `picDualDivisorClass_mulByInt` (L265, dead), `weilPairing_adjoint_of_naturality` (L314, dead).
  **No live consumer.**
- **Visibility**: public. **Lines**: 213–229, ~4 lines.
- **DEAD.** Mirror: `SeparableScaling.pullbackDivisorClass_image_noδ` (L512).

### `theorem picDualDivisorClass_mulByInt`  — **DEAD/SUPERSEDED**
- **Type**: `[IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)`, `ch`/`hinj`/`hfin`, `hnat`, `hsurjDual`, `hsurj`,
  `hcard : ℓ² = finrank R R`; concludes `PicDualDivisorClass W (mulByInt W.toAffine ℓ) ch hinj hfin`.
- **What**: the `[ℓ]` instance of `PicDualDivisorClass` (Silverman III.6.1b for multiplication-by-`ℓ`).
- **How**: `picDualDivisorClass_of_naturality` with `#ker[ℓ] = ℓ²` (`nat_card_mulByInt_ker`).
- **Uses from project**: `picDualDivisorClass_of_naturality` (this file), `nat_card_mulByInt_ker`,
  `mulByInt`, `Naturality`, `picDual`.
- **Used by**: **nothing.** (Note: requires `(mulByInt ℓ).CoordHom`, which per `MEMORY.md` does not exist —
  so it is not just unused but **uninstantiable**.)
- **Visibility**: public. **Lines**: 252–268, ~3 lines.
- **DEAD/UNINSTANTIABLE.** Mirror: the `δ`-based `weilPairing_scaling_noδ` etc. in `SeparableScaling.lean`.

### `theorem weilPairing_adjoint_of_naturality`  — **DEAD/SUPERSEDED**
- **Type**: the separable Weil-pairing adjoint `e_ℓ(φS, T) = e_ℓ(S, φ̂T)` (φ̂ = `picDual φ`) from `ProjOrdTransport`,
  the `[ℓ]`/`φ` commutation, the III.3.4/III.6.2(a) dual data, and `hcomm'`.
- **What**: the adjoint with the `PicDualDivisorClass` hypothesis discharged from naturality witnesses.
- **How**: term-mode `weilPairing_adjoint_of_picDualDivisorClass` fed by `picDualDivisorClass_of_naturality`.
- **Uses from project**: `weilPairing_adjoint_of_picDualDivisorClass` (HfactLemma),
  `picDualDivisorClass_of_naturality` (this file), `weilPairing`, `Isogeny.picDual`, `ProjOrdTransport`,
  `Naturality`, `translateAlgEquivOfPoint`, `weilFunction`, `mulByInt`.
- **Used by**: **nothing.** (Carries the `picDual φ` codomain — only instantiable with a CoordHom.)
- **Visibility**: public. **Lines**: 291–315, ~3 lines (term-mode; large signature).
- **DEAD.** Mirror: `SeparableScaling.weilPairing_adjoint_of_dualComp` (L308) / `weilPairing_adjoint_image_noδ`
  (L587) — the CoordHom-free adjoints actually used.

---

## File Summary

- **Role in proof**: Only the **first three (primitive) lemmas** are on the live path — they are the
  σ-bridge-derived divisor facts consumed by `SeparableScaling.lean` (the live separable-scaling layer that
  feeds the per-`ℓ` `OneSubFrobeniusScaling` / pencil leaves and the capstone). The remaining five form a
  **historical picDual/CoordHom discharge chain** that was abandoned once the CoordHom-impossibility for
  `[ℓ]` was established; `SeparableScaling.lean` re-derives every one of them CoordHom-free with an abstract
  dual map `δ`.
- **(a) Dead/unused declarations** (named): `sigma_pullbackDivisor_kappaDivisor_eq_picDual`,
  `picDualDivisorClass_of_picDualComp`, `picDualDivisorClass_of_naturality`, `picDualDivisorClass_mulByInt`,
  `weilPairing_adjoint_of_naturality`. **No real consumers; safe to delete** (update the `SeparableScaling`
  docstrings that name them as "mirror originals" first).
- **(b) Scratch/superseded sub-routes**: the entire **picDual/CoordHom route** (Steps 2–5 + the adjoint) is
  superseded. `picDualDivisorClass_mulByInt` is moreover **uninstantiable** (no `(mulByInt ℓ).CoordHom`).
- **(c) Hand-rolled vs mathlib (divisor-class / Picard modelling)**: the project models divisor classes via
  its own `Curves.ProjectiveDivisor` / `projectiveDivisorSum` (Abel–Jacobi σ) + `projIsPrincipal_of_*` and a
  bespoke `Isogeny.picDual` (Pic⁰ dual). Mathlib has no elliptic-curve Picard / dual-isogeny API at this level,
  so hand-rolling is justified; but the **two parallel formulations** (`picDual φ` here vs abstract `δ` in
  `SeparableScaling`) are the moral-duplication cost of the abandoned route.
- **(d) Moral duplication**: each of the 5 dead decls has a 1:1 live mirror in `SeparableScaling.lean`
  (`*_eq_dual`, `*_of_dualComp`, `*_image_noδ`, adjoints). This is the single largest duplication finding in
  the cluster.
- **(e) Under-general statements**: the live trio is well-stated for general `AddMonoidHom`/`Isogeny φ`. The
  dead chain is *over-specialized* to carrying a `CoordHom` it cannot have.
- **Cleanup flags**: no `sorry`, no `maxHeartbeats`. Longest proof `picDualDivisorClass_of_picDualComp`
  (~13 lines, dead). Recommend deleting the 5 dead decls and retargeting `SeparableScaling`'s "mirror of …"
  docstrings.
