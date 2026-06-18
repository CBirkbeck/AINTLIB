# Inventory: ./HasseWeil/WeilPairing/OneSubWitnesses.lean

**Total file**: 470 lines, 12 declarations (all `theorem` or `noncomputable def`), 0 sorries, 0 `set_option maxHeartbeats`.

**Purpose**: Discharges the point/divisor witnesses of `OneSubScalingData` over `K̄` (CoordHom-free). Connects the abstract base-changed isogeny `(1 − π)_{K̄}` to the concrete geometric Frobenius, proves `finiteKer` and reduces `hkerdeg` and `hsurj` to named clean hypotheses, then assembles `OneSubScalingData` from only the still-open residuals.

---

## LIVE / DEAD classification (verified dependency analysis: 15/20 live for this file's "row")

The brief reports OneSubWitnesses as **15/20 live** (the "20" counts section-variable context lines
the analysis attributes here); of the **12 named declarations**, the genuinely-LIVE core (reached by
the live leaf-2 capstone `oneSubFrobeniusScaling_holds` via `OneSubProjOrdTransport.lean`) is the
**linchpin chain**:

- **LIVE (linchpin / kernel facts, on the live DAG)**: `isogeny_cast_apply_heq`,
  `some_heq_of_curve_eq`, `zero_heq_of_curve_eq`, `hns_iter`, `iterate_apply_some_heq`,
  `frobeniusHomBaseChange_eq_geomFrobeniusPoint`,
  `oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_oneSubGeomFrobHom`,
  `oneSubFrobeniusIsogBaseChange_finiteKer`,
  `oneSubFrobeniusIsogBaseChange_nat_card_ker_eq_pointCount`,
  `oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount`. The live leaf-2 path uses
  `…_finiteKer` (for the `Finite ker` instance), `…_hkerdeg_of_degree_eq_pointCount`, and the
  linchpin/HEq chain (transitively via `OneSubAffineResidues`/`OneSubInftyResidues`).
- **DEAD / SUPERSEDED (the δ-based assembly route, replaced by the δ-free `weilScales_noδ` route)**:
  `oneSubFrobeniusIsogBaseChange_hsurj_of_self_comp_dual` and `mkOneSubScalingDataConcrete_of_witnesses`.
  The live capstone is δ-free and surjectivity-free (`OneSubProjOrdTransport.oneSubFrobeniusScaling_holds`
  → `weilScales_noδ`), so the dual `δ`/`hself`-based `hsurj` reduction and the
  `OneSubScalingData` assembly are on the **superseded predecessor route**.
  (`…_hsurj_of_self_comp_dual` is *re-exported* by the also-superseded
  `SeparableWitnesses.oneSub_hsurj_of_self_comp_dual`, not by the live DAG.)

This matches the brief's "15/20 live": the two δ-route decls plus their section-context lines are the
dead remainder.

---

### `theorem isogeny_cast_apply_heq`

- **Type**: `{F : Type*} [Field F] [DecidableEq F] {A₁ A₂ A₂' : WeierstrassCurve F} [IsElliptic A₁] [IsElliptic A₂] [IsElliptic A₂'] (φ : Isogeny A₁.toAffine A₂.toAffine) (hcurve : A₂ = A₂') (hisog : Isogeny A₁.toAffine A₂.toAffine = Isogeny A₁.toAffine A₂'.toAffine) (P : A₁.toAffine.Point) : HEq ((cast hisog φ).toAddMonoidHom P) (φ.toAddMonoidHom P)`
- **What**: Proves that casting an isogeny along a propositional curve equality and then applying the point map is heterogeneously equal to applying the original point map; the cast is invisible up to `HEq`.
- **How**: `subst hcurve; rfl` — once the curve equality is substituted, both sides reduce to the same expression by definitional equality.
- **Hypotheses**: Codomain curve equality `A₂ = A₂'`; corresponding isogeny-type equality.
- **Uses from project**: none (pure `HEq`/`subst` infrastructure)
- **Used by**: `iterate_apply_some_heq` (2 times), `frobeniusHomBaseChange_eq_geomFrobeniusPoint` (2 times)
- **Visibility**: public
- **Lines**: 99–108, proof ~4 lines
- **Notes**: Key `HEq` cast-transport helper.

---

### `theorem some_heq_of_curve_eq`

- **Type**: `{F : Type*} [Field F] [DecidableEq F] {A A' : WeierstrassCurve F} [IsElliptic A] [IsElliptic A'] (hAA : A = A') {x y : F} (h : A.toAffine.Nonsingular x y) (h' : A'.toAffine.Nonsingular x y) : HEq (Affine.Point.some x y h : A.toAffine.Point) (Affine.Point.some x y h' : A'.toAffine.Point)`
- **What**: Proves that two `.some` points with the same coordinates are heterogeneously equal when the ambient curves are propositionally equal.
- **How**: `subst hAA; rfl`.
- **Hypotheses**: Curve equality `A = A'`; nonsingularity of `(x,y)` on both curves.
- **Uses from project**: none
- **Used by**: `iterate_apply_some_heq` (2 times), `frobeniusHomBaseChange_eq_geomFrobeniusPoint` (1 time)
- **Visibility**: public
- **Lines**: 109–116, proof ~3 lines
- **Notes**: None.

---

### `theorem zero_heq_of_curve_eq`

- **Type**: `{F : Type*} [Field F] [DecidableEq F] {A A' : WeierstrassCurve F} [IsElliptic A] [IsElliptic A'] (hAA : A = A') : HEq (0 : A.toAffine.Point) (0 : A'.toAffine.Point)`
- **What**: Proves heterogeneous equality of zero points across a curve equality.
- **How**: `subst hAA; rfl`.
- **Hypotheses**: Curve equality `A = A'`.
- **Uses from project**: none
- **Used by**: `frobeniusHomBaseChange_eq_geomFrobeniusPoint` (1 time)
- **Visibility**: public
- **Lines**: 118–122, proof ~2 lines
- **Notes**: None.

---

### `theorem hns_iter`

- **Type**: `(E : WeierstrassCurve K) [E.toAffine.IsElliptic] (n : ℕ) {x y : K} (h : E.toAffine.Nonsingular x y) : (E.map (iterateFrobenius K p n)).toAffine.Nonsingular (x ^ p ^ n) (y ^ p ^ n)`
- **What**: Nonsingularity of the coordinate-power point `(x^{p^n}, y^{p^n})` on the iterated Frobenius twist `E.map (iterateFrobenius K p n)`, given nonsingularity of `(x,y)` on `E`.
- **How**: Uses `WeierstrassCurve.Affine.map_nonsingular` (ring-hom nonsingularity transfer) with the fact that `iterateFrobenius K p n a = a^{p^n}` (`iterateFrobenius_def`), and injectivity of the iterate.
- **Hypotheses**: `K` is a field of characteristic `p` (prime); `(x,y)` nonsingular on `E`.
- **Uses from project**: none (uses mathlib's `WeierstrassCurve.Affine.map_nonsingular`, `iterateFrobenius_def`)
- **Used by**: `iterate_apply_some_heq` (1 time), `frobeniusHomBaseChange_eq_geomFrobeniusPoint` (1 time)
- **Visibility**: public
- **Lines**: 134–141, proof ~6 lines
- **Notes**: None.

---

### `theorem iterate_apply_some_heq`

- **Type**: `(E : WeierstrassCurve K) [E.toAffine.IsElliptic] (r : ℕ) (x y : K) (h : E.toAffine.Nonsingular x y) (h' : (E.map (iterateFrobenius K p r)).toAffine.Nonsingular (x ^ p ^ r) (y ^ p ^ r)) : HEq ((Isogeny.frobeniusIsog_relative_iterate p E r).toAddMonoidHom (.some x y h)) (Affine.Point.some (x ^ p ^ r) (y ^ p ^ r) h')`
- **What**: The iterated relative `p`-Frobenius isogeny sends an affine point `(x, y)` to `(x^{p^r}, y^{p^r})` on `E.map (iterateFrobenius K p r)`, stated as a `HEq` to handle the codomain cast.
- **How**: Induction on `r`. Base case: unfolds `frobeniusIsog_relative_iterate`, peels the `cast` via `isogeny_cast_apply_heq` (identity isogeny over `E.map id = E`), then uses `some_heq_of_curve_eq` to match coordinates. Inductive step: unfolds the iterate, applies `isogeny_cast_apply_heq` for the composition cast, rewrites using the inductive hypothesis (`hih` via `eq_of_heq`), applies `frobeniusIsog_relative_apply_some` for the outer Frobenius step, and closes with `some_heq_of_curve_eq` after computing `(x^{p^n})^p = x^{p^{n+1}}`.
- **Hypotheses**: `K` has characteristic `p` (prime); `(x,y)` nonsingular on `E`.
- **Uses from project**: `isogeny_cast_apply_heq` (2 times), `some_heq_of_curve_eq` (2 times), `hns_iter` (1 time); also mathlib `frobeniusIsog_relative_apply_some`, `iterateFrobenius_add`, `iterateFrobenius_one`, `iterateFrobenius_zero`, `WeierstrassCurve.map_map`, `WeierstrassCurve.map_id`
- **Used by**: `frobeniusHomBaseChange_eq_geomFrobeniusPoint` (1 time)
- **Visibility**: public
- **Lines**: 149–196, proof ~44 lines
- **Notes**: Proof longer than 30 lines. The main `HEq` chain driving the cast-peeling induction.

---

### `theorem frobeniusHomBaseChange_eq_geomFrobeniusPoint`

- **Type**: `[(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic] : frobeniusHomBaseChange W p r (AlgebraicClosure K) = geomFrobeniusPoint W`
- **What**: Over the algebraic closure, the base-changed Frobenius point map `frobeniusHomBaseChange` (the iterated relative `p`-Frobenius carried through a cast) equals the geometric Frobenius `geomFrobeniusPoint` (the literal `q`-power on coordinates via `frobeniusAlgHom`).
- **How**: Cases on `P : (W.baseChange K̄).toAffine.Point`. For `0`: unfolds `frobeniusIsog_baseChange_charP_pow`, uses `isogeny_cast_apply_heq` to strip the outer cast, rewrites `map_zero`, closes via `zero_heq_of_curve_eq` and `geomFrobeniusPointFun_zero`. For `.some x y h`: unfolds the same, applies `isogeny_cast_apply_heq`, chains `iterate_apply_some_heq` (to get `(x^{p^r}, y^{p^r})`), then `geomFrobeniusPointFun_some` and `FiniteField.coe_frobeniusAlgHom` (using `#K = p^r`) to match coordinates via `some_heq_of_curve_eq`.
- **Hypotheses**: `K` finite, `CharP K p`, `Fintype.card K = p^r`.
- **Uses from project**: `isogeny_cast_apply_heq` (2 times), `zero_heq_of_curve_eq` (1 time), `hns_iter` (1 time), `iterate_apply_some_heq` (1 time), `some_heq_of_curve_eq` (1 time); also mathlib `Isogeny.frobeniusTwistIterate_baseChange_eq_self_of_charP_pow`, `geomFrobeniusPointFun_some`, `geomFrobeniusPointFun_zero`, `FiniteField.coe_frobeniusAlgHom`
- **Used by**: `oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_oneSubGeomFrobHom` (1 time)
- **Visibility**: public
- **Lines**: 217–257, proof ~38 lines
- **Notes**: Proof longer than 30 lines. This is the "linchpin" theorem of the file, stated as axiom-clean in the module docstring.

---

### `theorem oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_oneSubGeomFrobHom`

- **Type**: `[(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic] (pullback_L : ...) : (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) pullback_L).toAddMonoidHom = oneSubGeomFrobHom W`
- **What**: The point map of the base-changed `(1 − π)_{K̄}` isogeny equals `oneSubGeomFrobHom W` (the additive map `id − geomFrobenius`).
- **How**: Rewrites via `oneSubFrobeniusIsogBaseChange_toAddMonoidHom` (structural identity) and then `frobeniusHomBaseChange_eq_geomFrobeniusPoint` (the linchpin), closing with `rfl`.
- **Hypotheses**: IsElliptic instance for `W.baseChange K̄`; function-field pullback `pullback_L`.
- **Uses from project**: `oneSubFrobeniusIsogBaseChange_toAddMonoidHom` (from `IsogenyBaseChangeConcrete`), `frobeniusHomBaseChange_eq_geomFrobeniusPoint` (this file)
- **Used by**: `oneSubFrobeniusIsogBaseChange_finiteKer`, `oneSubFrobeniusIsogBaseChange_nat_card_ker_eq_pointCount`
- **Visibility**: public
- **Lines**: 261–268, proof ~3 lines
- **Notes**: None.

---

### `theorem oneSubFrobeniusIsogBaseChange_finiteKer`

- **Type**: `[(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic] (pullback_L : ...) : Finite (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) pullback_L).toAddMonoidHom.ker`
- **What**: The kernel of `(1 − π)_{K̄}` is a finite subgroup.
- **How**: Rewrites the kernel via `oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_oneSubGeomFrobHom`, then identifies the underlying set as `Set.range (includePointBC W)` using `ker_oneSubGeomFrobHom_eq_fixedLocus` and `fixedLocus_geomFrobenius_eq_range_includePointBC` (from `FrobeniusFixedPoint.lean`); finiteness follows from `Set.finite_range` (the range of a map from the finite set `W.toAffine.Point`).
- **Hypotheses**: `K` finite, characteristic `p`, `#K = p^r`; IsElliptic and Fintype instances.
- **Uses from project**: `oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_oneSubGeomFrobHom` (this file), `ker_oneSubGeomFrobHom_eq_fixedLocus` (`FrobeniusFixedPoint`), `fixedLocus_geomFrobenius_eq_range_includePointBC` (`FrobeniusFixedPoint`), `includePointBC` (`FrobeniusFixedPoint`)
- **Used by**: `mkOneSubScalingDataConcrete_of_witnesses` (1 time)
- **Visibility**: public
- **Lines**: 288–299, proof ~8 lines
- **Notes**: None.

---

### `theorem oneSubFrobeniusIsogBaseChange_nat_card_ker_eq_pointCount`

- **Type**: `[(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic] (pullback_L : ...) : Nat.card (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) pullback_L).toAddMonoidHom.ker = pointCount W.toAffine`
- **What**: The cardinality of the kernel of `(1 − π)_{K̄}` equals the number of `𝔽_q`-rational points on `E`.
- **How**: Rewrites via `oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_oneSubGeomFrobHom`, converts `Nat.card` on the subtype to set `ncard`, then applies `ncard_ker_oneSubGeomFrobHom_eq_pointCount` (from `FrobeniusFixedPoint.lean`).
- **Hypotheses**: Same as `oneSubFrobeniusIsogBaseChange_finiteKer`.
- **Uses from project**: `oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_oneSubGeomFrobHom` (this file), `ncard_ker_oneSubGeomFrobHom_eq_pointCount` (`FrobeniusFixedPoint`), `pointCount`
- **Used by**: `oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount` (1 time)
- **Visibility**: public
- **Lines**: 304–315, proof ~7 lines
- **Notes**: None.

---

### `theorem oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount`

- **Type**: `[(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic] (pullback_L : ...) (hdeg_eq : (oneSubFrobeniusIsogBaseChange ...).degree = pointCount W.toAffine) : Nat.card (...).toAddMonoidHom.ker = (...).degree`
- **What**: The `hkerdeg` witness (`#ker = deg φ`) for `(1 − π)_{K̄}`, reduced to V.1.3: once the degree identity `deg = pointCount` is supplied as a hypothesis, the result follows from the proved cardinality `#ker = pointCount`.
- **How**: Rewrites `#ker` via `oneSubFrobeniusIsogBaseChange_nat_card_ker_eq_pointCount`, then substitutes `hdeg_eq`.
- **Hypotheses**: V.1.3 degree identity `hdeg_eq` (carries `sorryAx` upstream); other standard instances.
- **Uses from project**: `oneSubFrobeniusIsogBaseChange_nat_card_ker_eq_pointCount` (this file), `pointCount`
- **Used by**: `mkOneSubScalingDataConcrete_of_witnesses` (1 time)
- **Visibility**: public
- **Lines**: 327–336, proof ~2 lines
- **Notes**: This lemma is itself axiom-clean; `sorryAx` enters only when the caller supplies `hdeg_eq` from `isogOneSub_negFrobenius_degree_eq_pointCount` (V.1.3).

---

### `theorem oneSubFrobeniusIsogBaseChange_hsurj_of_self_comp_dual`

- **Type**: `[(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic] (pullback_L : ...) (δ : E(K̄).Point →+ E(K̄).Point) (N : ℤ) (hN : (N : K̄) ≠ 0) (hself : φ.toAddMonoidHom.comp δ = (mulByInt E N).toAddMonoidHom) : Function.Surjective φ.toAddMonoidHom`
- **What**: Surjectivity of `(1 − π)_{K̄}` from the dual composition `φ ∘ δ = [N]`: given `Q`, pick `R` with `[N]R = Q` (via `mulByInt_point_surjective`, Silverman III.4.10b over `K̄`), then `φ(δR) = [N]R = Q`.
- **How**: For any `Q`, obtains `R` such that `[N]R = Q` via `mulByInt_point_surjective` (uses `hN`); the witness is `δR`; the equality `φ(δR) = Q` follows from `hself` pointwise via `DFunLike.congr_fun` and `mulByInt_apply`.
- **Hypotheses**: `(N : K̄) ≠ 0`; the dual composition equality `hself`.
- **Uses from project**: `mulByInt_point_surjective` (from the project's torsion/isogeny API), `mulByInt_apply`
- **Used by**: `mkOneSubScalingDataConcrete_of_witnesses` (1 time)
- **Visibility**: public
- **Lines**: 354–373, proof ~9 lines
- **Notes**: None.

---

### `noncomputable def mkOneSubScalingDataConcrete_of_witnesses`

- **Type**: `(hq : 2 ≤ Fintype.card K) (hdeg_eq : ...) (hproj : ProjOrdTransport ...) (δ : E(K̄).Point →+ E(K̄).Point) (hdc : δ.comp φ.toAddMonoidHom = [N]) (hself : φ.toAddMonoidHom.comp δ = [N]) (hNne : (N : K̄) ≠ 0) (hcomm' : ...) : OneSubScalingData W p r (AlgebraicClosure K) hq`
- **What**: Assembles the full `OneSubScalingData` over `K̄ = AlgebraicClosure K`, supplying only the genuinely-open divisor-level witnesses (`hproj`, `δ`/`hdc`/`hself` as an `IsDualOf`, `hcomm'`, `hdeg_eq`). Internally discharges: `pullback_L` (via `oneSubFrobeniusPullback_L`), `finiteKer`, `hkerdeg` (from `hdeg_eq`), and `hsurj` (from `hself`).
- **How**: Delegates to `mkOneSubScalingDataConcrete`, filling: `finiteKer` via `oneSubFrobeniusIsogBaseChange_finiteKer`, `hsurj` via `oneSubFrobeniusIsogBaseChange_hsurj_of_self_comp_dual`, `hkerdeg` via `oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount`.
- **Hypotheses**: `2 ≤ #K`; V.1.3 degree identity `hdeg_eq`; `ProjOrdTransport` for the isogeny; dual `δ` with both composition identities `hdc`/`hself`; non-zero characteristic condition `hNne`; translation covariance `hcomm'`; IsIntegrallyClosed and IsElliptic instances.
- **Uses from project**: `oneSubFrobeniusPullback_L` (`IsogenyBaseChangeConcrete`), `mkOneSubScalingDataConcrete` (`IsogenyBaseChangeConcrete`), `oneSubFrobeniusIsogBaseChange_finiteKer` (this file), `oneSubFrobeniusIsogBaseChange_hsurj_of_self_comp_dual` (this file), `oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount` (this file), `ProjOrdTransport`, `mulByInt`, `translateAlgEquivOfPoint`, `weilFunction`, `OneSubScalingData`, `pointCount`
- **Used by**: unused in file (leaf export for callers in other files)
- **Visibility**: public
- **Lines**: 412–466, proof ~9 lines (term-mode construction)
- **Notes**: The main API export of this file. `sorryAx` is inherited from `hdeg_eq` (V.1.3) when callers wire it up.

---

## Summary

| Declaration | Kind | Lines | Proof lines | Sorry |
|---|---|---|---|---|
| `isogeny_cast_apply_heq` | theorem | 99–108 | ~4 | no |
| `some_heq_of_curve_eq` | theorem | 109–116 | ~3 | no |
| `zero_heq_of_curve_eq` | theorem | 118–122 | ~2 | no |
| `hns_iter` | theorem | 134–141 | ~6 | no |
| `iterate_apply_some_heq` | theorem | 149–196 | ~44 | no |
| `frobeniusHomBaseChange_eq_geomFrobeniusPoint` | theorem | 217–257 | ~38 | no |
| `oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_oneSubGeomFrobHom` | theorem | 261–268 | ~3 | no |
| `oneSubFrobeniusIsogBaseChange_finiteKer` | theorem | 288–299 | ~8 | no |
| `oneSubFrobeniusIsogBaseChange_nat_card_ker_eq_pointCount` | theorem | 304–315 | ~7 | no |
| `oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount` | theorem | 327–336 | ~2 | no |
| `oneSubFrobeniusIsogBaseChange_hsurj_of_self_comp_dual` | theorem | 354–373 | ~9 | no |
| `mkOneSubScalingDataConcrete_of_witnesses` | noncomputable def | 412–466 | ~9 | no |

**Key API**: `isogeny_cast_apply_heq` (used by 4 declarations), `some_heq_of_curve_eq` (used by 3 declarations).

**Long proofs**: `iterate_apply_some_heq` (~44 lines), `frobeniusHomBaseChange_eq_geomFrobeniusPoint` (~38 lines).

**Unused in file**: `mkOneSubScalingDataConcrete_of_witnesses` (the main export, consumed by callers outside this file).
