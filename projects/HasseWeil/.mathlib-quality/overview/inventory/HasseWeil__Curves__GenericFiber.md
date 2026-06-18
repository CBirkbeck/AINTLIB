# Inventory: ./HasseWeil/Curves/GenericFiber.lean

**File purpose**: T-II-2-009 / Silverman II.2.6(b) — algebraic-geometric content of the generic-fiber cardinality theorem. For a nonconstant `CurveMap φ : C₁ → C₂`, the fiber `φ⁻¹(Q)` has cardinality `sepDeg(φ)` for almost all `Q`. The file provides the algebraic direction (ramification/inertia witnesses → fiber count) plus abstract Dedekind lemmas (Pieces 1–5) and curve-geometric support (Pieces 6–8).

**Imports**: `HasseWeil.Curves.CurveMap`, `HasseWeil.Curves.SmoothPointPrime`, `Mathlib.NumberTheory.RamificationInertia.Unramified`, `Mathlib.RingTheory.DedekindDomain.Different`, `Mathlib.RingTheory.DedekindDomain.Factorization`, `Mathlib.FieldTheory.IsAlgClosed.Basic`.

**Total declarations**: 12 theorems, 0 defs, 0 instances. No `sorry`.

---

## Namespace `HasseWeil.Curves.CurveMap`

---

### `theorem primesOverFinset_card_eq_degree_of_unramified`

- **Type**: Given `φ : CurveMap C₁ C₂` with `CoordHom`, `Module.Finite`, `IsIntegrallyClosed` on both coordinate rings, and a nonzero maximal ideal `p` of `C₂.CoordinateRing` such that every prime `P` above `p` in `C₁.CoordinateRing` satisfies `e_P · f_P = 1`, then `(primesOverFinset p C₁.CoordinateRing).card = φ.degree`.
- **What**: T-II-2-009 algebraic direction: an unramified prime with trivial residue degrees has fiber count equal to the degree.
- **How**: Applies `φ.sum_ramificationIdx_mul_inertiaDeg_eq_degree` (from `CurveMap.lean`) to get `Σ(e·f) = deg`; replaces each `e·f` by `1` via `h_ef_one`; rewrites `Σ 1 = |S|` using `Finset.sum_const` and `Nat.smul_one_eq_cast`.
- **Hypotheses**: Both coordinate rings integrally closed; algebra of `C₁.CR` over `C₂.CR` is module-finite; `p` nonzero maximal; all `e_P · f_P = 1` for primes above `p`.
- **Uses from project**: `CurveMap.sum_ramificationIdx_mul_inertiaDeg_eq_degree`, `primesOverFinset`.
- **Used by**: `primesOverFinset_card_eq_sepDegree_of_separable_and_unramified` (line 116), `exists_heightOneSpectrum_fiber_card_eq_sepDegree` (via `primesOverFinset_card_eq_sepDegree_of_separable_and_unramified`).
- **Visibility**: public
- **Lines**: 57–80; proof body ≈ 10 lines
- **Notes**: `set_option synthInstance.maxHeartbeats 200000` and `set_option maxHeartbeats 1600000` applied immediately before (lines 49–50); NO justifying comment present (NO-COMMENT).

---

### `theorem primesOverFinset_card_eq_sepDegree_of_separable_and_unramified`

- **Type**: Same hypotheses as above plus `FiniteDimensional` on function fields and `φ.IsSeparable`; concludes `(primesOverFinset p C₁.CoordinateRing).card = φ.separableDegree`.
- **What**: Separable case of T-II-2-009: converts the degree conclusion to separable degree using `sepDeg = deg` for separable extensions.
- **How**: Derives `φ.degree = φ.separableDegree` by showing `inseparableDegree = 1` (from `hsep`), using `Field.finSepDegree_dvd_finrank` and `Nat.eq_of_dvd_of_div_eq_one`. Then delegates to `primesOverFinset_card_eq_degree_of_unramified`.
- **Hypotheses**: Same as above plus `FiniteDimensional` on function fields and `φ.IsSeparable`.
- **Uses from project**: `primesOverFinset_card_eq_degree_of_unramified`, `CurveMap.separableDegree`, `CurveMap.inseparableDegree`, `CurveMap.degree`.
- **Used by**: `exists_heightOneSpectrum_fiber_card_eq_sepDegree` (line 426).
- **Visibility**: public
- **Lines**: 86–117; proof body ≈ 13 lines
- **Notes**: No `set_option`. The equality `degree / separableDegree = inseparableDegree` is used informally as `hdiv = hinsep`; the exact mathlib spelling (`inseparableDegree` as a `Nat` quotient) is noteworthy.

---

## Namespace `_root_` (IsDedekindDomain)

---

### `theorem IsDedekindDomain.finite_ramified_primes`

- **Type**: For a finite separable extension of Dedekind domains `A → B` (with `Module.IsTorsionFree`, `FaithfulSMul`), the set `{P : HeightOneSpectrum B | P.asIdeal ∣ differentIdeal A B}` is finite.
- **What**: T-II-2-009 Piece 1: the bad (ramified) locus in `HeightOneSpectrum B` is finite. Silverman's "finitely many bad Q".
- **How**: Sets up the fraction-ring algebra and scalar tower from `FractionRing.liftAlgebra`, then applies mathlib's `Ideal.finite_factors` to `differentIdeal_ne_bot`.
- **Hypotheses**: `A`, `B` Dedekind domains; `A → B` algebra; `Module.Finite A B`; `Module.IsTorsionFree A B`; `FaithfulSMul A B`; fraction-ring extension separable.
- **Uses from project**: (none — purely mathlib)
- **Used by**: `IsDedekindDomain.exists_unramified_prime` (line 210).
- **Visibility**: public (`_root_` namespace)
- **Lines**: 130–144; proof body ≈ 7 lines
- **Notes**: No `set_option`. Thin wrapper around mathlib's `Ideal.finite_factors` + `differentIdeal_ne_bot`.

---

### `theorem IsDedekindDomain.isUnramifiedAt_of_not_dvd_differentIdeal`

- **Type**: For `P : Ideal B` prime, if `¬ P ∣ differentIdeal A B`, then `Algebra.IsUnramifiedAt A P`.
- **What**: T-II-2-009 Piece 2: a prime not dividing the different ideal is unramified. Direct packaging of mathlib's `not_dvd_differentIdeal_iff`.
- **How**: Sets up fraction-ring algebra + scalar tower, then applies `not_dvd_differentIdeal_iff.mp hnd`.
- **Hypotheses**: Same Dedekind hypotheses as `finite_ramified_primes`; `P` is a prime ideal of `B` not dividing `differentIdeal A B`.
- **Uses from project**: (none)
- **Used by**: `IsDedekindDomain.exists_unramified_prime` (line 231).
- **Visibility**: public
- **Lines**: 153–167; proof body ≈ 7 lines
- **Notes**: No `set_option`. Thin wrapper.

---

### `theorem IsDedekindDomain.ramificationIdx_eq_one_of_isUnramifiedAt_of_ne_bot`

- **Type**: For `P : Ideal B` prime, `[Algebra.IsUnramifiedAt A P]`, `P ≠ ⊥`, concludes `Ideal.ramificationIdx (algebraMap A B) (P.under A) P = 1`.
- **What**: T-II-2-009 Piece 3 (ramification half): an unramified prime has ramification index 1.
- **How**: One-liner delegation to `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt hP`.
- **Hypotheses**: `A`, `B` as above (no Dedekind needed, only NoetherianRing + EssFiniteType); `P` prime, nonzero, unramified.
- **Uses from project**: (none)
- **Used by**: `IsDedekindDomain.exists_unramifiedPrime_ramificationIdx_eq_one` (line 269).
- **Visibility**: public
- **Lines**: 180–186; proof body = 1 line (term-mode)
- **Notes**: No `set_option`. Note the weaker typeclass assumptions than the other Piece theorems.

---

### `theorem IsDedekindDomain.exists_unramified_prime`

- **Type**: Under same Dedekind + finite separable hypotheses plus `hinf : Set.Infinite {P : HeightOneSpectrum B | True}`, produces `P : HeightOneSpectrum B` with `Algebra.IsUnramifiedAt A P.asIdeal`.
- **What**: T-II-2-009 Piece 4: from finiteness of bad locus (Piece 1) and infiniteness of the spectrum, extract an unramified prime.
- **How**: Applies `finite_ramified_primes` for `hfin_bad`; argues by contradiction that the good set is nonempty (if every prime divides differentIdeal, the total set would be finite, contradicting `hinf`); then applies `isUnramifiedAt_of_not_dvd_differentIdeal`.
- **Hypotheses**: Dedekind A→B, finite separable, and `HeightOneSpectrum B` infinite.
- **Uses from project**: `IsDedekindDomain.finite_ramified_primes` (line 210), `IsDedekindDomain.isUnramifiedAt_of_not_dvd_differentIdeal` (line 231).
- **Used by**: `IsDedekindDomain.exists_unramifiedPrime_ramificationIdx_eq_one` (line 265).
- **Visibility**: public
- **Lines**: 200–231; proof body ≈ 20 lines
- **Notes**: No `set_option`. Uses `by_contra` + set-membership argument; `Set.not_nonempty_iff_eq_empty` + `Set.Infinite.subset`.

---

### `theorem IsDedekindDomain.exists_unramifiedPrime_ramificationIdx_eq_one`

- **Type**: Under same hypotheses plus `[Algebra.EssFiniteType A B]` and infinite spectrum, produces `P : HeightOneSpectrum B` with `ramificationIdx (algebraMap A B) (P.asIdeal.under A) P.asIdeal = 1`.
- **What**: T-II-2-009 Piece 5: composes Pieces 1–4 to give an explicit prime with ramification index 1.
- **How**: Obtains unramified prime via `exists_unramified_prime`; applies `ramificationIdx_eq_one_of_isUnramifiedAt_of_ne_bot` using `P.ne_bot`.
- **Hypotheses**: Dedekind A→B finite separable, `EssFiniteType`, infinite spectrum.
- **Uses from project**: `IsDedekindDomain.exists_unramified_prime` (line 265), `IsDedekindDomain.ramificationIdx_eq_one_of_isUnramifiedAt_of_ne_bot` (line 269).
- **Used by**: unused in file; consumed by `ResidueFieldAtSmoothPoint.lean` (externally).
- **Visibility**: public
- **Lines**: 254–269; proof body ≈ 7 lines
- **Notes**: No `set_option`.

---

## Namespace `HasseWeil.Curves.SmoothPlaneCurve`

---

### `theorem exists_smoothPoint_of_x`

- **Type**: `[IsAlgClosed F]`, `C : SmoothPlaneCurve F`, `[C.toAffine.IsElliptic]`, `x : F` → `∃ P : C.SmoothPoint, P.x = x`.
- **What**: T-II-2-009 Piece 6 (support): for every x-coordinate over an algebraically closed field, the Weierstrass equation in `y` has a root, giving a smooth point with that x-coordinate.
- **How**: Constructs the y-polynomial `Y² + (a₁x+a₃)Y − (x³+a₂x²+a₄x+a₆)`, shows it has degree 2 and nonzero via `compute_degree!`; extracts a root via `IsAlgClosed.exists_root`; checks `WeierstrassCurve.Affine.equation_iff'` via `linear_combination`, and nonsingularity via `WeierstrassCurve.Affine.equation_iff_nonsingular` (which for elliptic curves is automatic from the equation).
- **Hypotheses**: `F` algebraically closed; `C` smooth plane curve with `IsElliptic`.
- **Uses from project**: (mathlib only: `WeierstrassCurve.Affine.equation_iff'`, `WeierstrassCurve.Affine.equation_iff_nonsingular`, `IsAlgClosed.exists_root`)
- **Used by**: `smoothPoint_infinite` (lines 329, 331, 332, 333, 334).
- **Visibility**: public
- **Lines**: 291–319; proof body ≈ 29 lines
- **Notes**: No `set_option`. Uses `set` to name the y-polynomial; relies on `equation_iff_nonsingular` which works for elliptic curves (Δ≠0). Proof length = 29 lines (just under threshold). Uses `linear_combination` to close the equation check.

---

### `theorem smoothPoint_infinite`

- **Type**: `[IsAlgClosed F]`, `C : SmoothPlaneCurve F`, `[C.toAffine.IsElliptic]` → `Infinite C.SmoothPoint`.
- **What**: T-II-2-009 Piece 6: the smooth-point set is infinite over an algebraically closed base, via an injection `F → C.SmoothPoint` sending `x` to the chosen smooth point at that x-coordinate.
- **How**: Uses `Infinite.of_injective` with the map `x ↦ (exists_smoothPoint_of_x C x).choose`; injectivity from comparing x-coordinates via `choose_spec`.
- **Hypotheses**: `F` algebraically closed; `C` elliptic.
- **Uses from project**: `exists_smoothPoint_of_x` (lines 329, 331–334).
- **Used by**: `heightOneSpectrum_infinite` (line 348).
- **Visibility**: public
- **Lines**: 324–337; proof body ≈ 10 lines
- **Notes**: No `set_option`.

---

### `theorem heightOneSpectrum_infinite`

- **Type**: `[IsAlgClosed F]`, `C : SmoothPlaneCurve F`, `[C.toAffine.IsElliptic]`, `[IsIntegrallyClosed C.CoordinateRing]` → `Set.Infinite {P : IsDedekindDomain.HeightOneSpectrum C.CoordinateRing | True}`.
- **What**: T-II-2-009 Piece 6 (main): the height-one spectrum of the coordinate ring is infinite, via the bijection `SmoothPoint ≃ HeightOneSpectrum`.
- **How**: Derives `Infinite C.SmoothPoint` from `smoothPoint_infinite`; lifts via `Infinite.of_injective C.smoothPointEquivHeightOneSpectrum ...injective`; concludes `Set.infinite_univ`.
- **Hypotheses**: `F` algebraically closed; `C` elliptic; coordinate ring integrally closed.
- **Uses from project**: `smoothPoint_infinite` (line 348), `SmoothPlaneCurve.smoothPointEquivHeightOneSpectrum` (lines 350–351).
- **Used by**: unused in file; consumed by `ResidueFieldAtSmoothPoint.lean` (line 341, externally).
- **Visibility**: public
- **Lines**: 343–352; proof body ≈ 6 lines
- **Notes**: No `set_option`.

---

## Namespace `HasseWeil.Curves.CurveMap` (continued)

---

### `theorem finrank_quotientMaximalIdealAt_eq_one`

- **Type**: `(C : SmoothPlaneCurve F) (P : C.SmoothPoint)` → `Module.finrank F (C.CoordinateRing ⧸ C.maximalIdealAt P) = 1`.
- **What**: T-II-2-009 Piece 7: the residue field at a smooth point has F-rank 1 (i.e., equals F). Direct re-export of `NormValuation.finrank_quotientMaximalIdealAt`.
- **How**: One-line delegation to `C.finrank_quotientMaximalIdealAt P`.
- **Hypotheses**: None beyond `C` smooth plane curve and `P` smooth point.
- **Uses from project**: `SmoothPlaneCurve.finrank_quotientMaximalIdealAt` (from `NormValuation.lean`, line 60).
- **Used by**: unused in file (consumed externally as documented in Piece 7 comment).
- **Visibility**: public
- **Lines**: 374–377; proof body = 1 line (term-mode)
- **Notes**: No `set_option`. Thin re-export; diamond between `Module.Free` paths (described in Piece 9 note) explains why `inertiaDeg = 1` is not proven directly.

---

### `theorem exists_heightOneSpectrum_fiber_card_eq_sepDegree`

- **Type**: Given `φ : CurveMap C₁ C₂` with `CoordHom`, `Module.Finite`, `FiniteDimensional` on function fields, `φ.IsSeparable`, a `Q : HeightOneSpectrum C₂.CoordinateRing`, and `h_ef_one_Q` asserting all `e_P · f_P = 1` for primes above `Q.asIdeal`, produces `(primesOverFinset Q.asIdeal C₁.CoordinateRing).card = φ.separableDegree`.
- **What**: T-II-2-009 Piece 8 (full assembly, witness form): given a concrete unramified prime `Q` with trivial residue degrees, the fiber cardinality equals `separableDegree`. The "witnessing" form leaves the residue-degree hypothesis to the caller.
- **How**: Derives `Q.asIdeal.IsMaximal` from `Q.isPrime.isMaximal Q.ne_bot`; then delegates to `primesOverFinset_card_eq_sepDegree_of_separable_and_unramified`.
- **Hypotheses**: Both coordinate rings integrally closed; `Module.Finite` + `FiniteDimensional` for the function-field extension; `φ.IsSeparable`; `Q` a `HeightOneSpectrum` element; all `e_P · f_P = 1` for primes above `Q.asIdeal`.
- **Uses from project**: `primesOverFinset_card_eq_sepDegree_of_separable_and_unramified` (line 426).
- **Used by**: unused in file; consumed by `ResidueFieldAtSmoothPoint.lean` (line 360, externally).
- **Visibility**: public
- **Lines**: 405–427; proof body ≈ 6 lines
- **Notes**: No `set_option`. The comment explains the `inertiaDeg = 1` diamond (Piece 9) that prevents a fully unconditional form. The unconditional version `exists_heightOneSpectrum_fiber_card_eq_sepDegree_unconditional` lives in `ResidueFieldAtSmoothPoint.lean`.

---

## Summary of cross-references within file

| Declaration | Used by (in file) |
|---|---|
| `primesOverFinset_card_eq_degree_of_unramified` | `primesOverFinset_card_eq_sepDegree_of_separable_and_unramified` |
| `primesOverFinset_card_eq_sepDegree_of_separable_and_unramified` | `exists_heightOneSpectrum_fiber_card_eq_sepDegree` |
| `IsDedekindDomain.finite_ramified_primes` | `IsDedekindDomain.exists_unramified_prime` |
| `IsDedekindDomain.isUnramifiedAt_of_not_dvd_differentIdeal` | `IsDedekindDomain.exists_unramified_prime` |
| `IsDedekindDomain.ramificationIdx_eq_one_of_isUnramifiedAt_of_ne_bot` | `IsDedekindDomain.exists_unramifiedPrime_ramificationIdx_eq_one` |
| `IsDedekindDomain.exists_unramified_prime` | `IsDedekindDomain.exists_unramifiedPrime_ramificationIdx_eq_one` |
| `exists_smoothPoint_of_x` | `smoothPoint_infinite` |
| `smoothPoint_infinite` | `heightOneSpectrum_infinite` |

## Key API (used by 3+ declarations in file)

- `primesOverFinset` (from `CurveMap.lean`): referenced in 4 declarations (Pieces 1, 2, 8, and in the type of `sum_ramificationIdx_mul_inertiaDeg_eq_degree`).
- `primesOverFinset_card_eq_sepDegree_of_separable_and_unramified`: used by `exists_heightOneSpectrum_fiber_card_eq_sepDegree` and itself uses `primesOverFinset_card_eq_degree_of_unramified` — chain of 3.

## Notable observations

- **No `sorry`** in the file.
- **`set_option maxHeartbeats 1600000`** (line 50) and `set_option synthInstance.maxHeartbeats 200000` (line 49) apply only to `primesOverFinset_card_eq_degree_of_unramified`; NO justifying comment.
- **Piece 9** (inertiaDeg = 1) is deliberately left as a comment documenting a `Module.Free` typeclass diamond; no declaration is attempted.
- All five `_root_.IsDedekindDomain.*` lemmas are thin wrappers around mathlib (`Ideal.finite_factors`, `not_dvd_differentIdeal_iff`, `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`); they exist mainly to package the fraction-ring algebra setup.
- The unconditional assembly (`exists_heightOneSpectrum_fiber_card_eq_sepDegree_unconditional`) was moved to `ResidueFieldAtSmoothPoint.lean`, which imports this file.
