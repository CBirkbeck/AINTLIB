# Inventory: ./HasseWeil/WeilPairing/DivisorGalois.lean

**File purpose**: Adic-valuation transport under a ring isomorphism — the algebraic engine for
divisor-Galois-descent (`div(σ f) = σ_*(div f)`), plus geometric bookkeeping lemmas for transporting
`pointValuation`, `ord_P`, and `ordAtInfty` through curve-equality `RingEquiv.cast`.

**Imports**: `Mathlib.RingTheory.DedekindDomain.AdicValuation`, `Mathlib.RingTheory.Localization.FractionRing`,
`Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`, `HasseWeil.Curves.Valuation`, `HasseWeil.Curves.Infinity`.

**Namespace**: `HasseWeil.WeilPairing`

---

## Section `IdealTransport`

### `theorem map_le_map_iff_ringEquiv`
- **Type**: `(Φ : R ≃+* R') (A B : Ideal R) : Ideal.map Φ.toRingHom A ≤ Ideal.map Φ.toRingHom B ↔ A ≤ B`
- **What**: `Ideal.map Φ` is an order embedding (both-direction ≤) for a ring isomorphism `Φ`.
- **How**: The forward direction uses `Ideal.comap_mono` followed by two applications of
  `Ideal.comap_map_of_bijective` (surjectivity of Φ) to cancel the comap-map roundtrip. The reverse
  direction is `Ideal.map_mono`.
- **Hypotheses**: R, R' are Dedekind domains (CommRing, IsDomain, IsDedekindDomain). `Φ` is a ring iso.
- **Uses from project**: none
- **Used by**: `map_prime_ringEquiv`, `map_ne_bot_ringEquiv`
- **Visibility**: public
- **Lines**: 56–63, proof ~7 lines
- **Notes**: None

---

### `theorem map_prime_ringEquiv`
- **Type**: `(Φ : R ≃+* R') (p : Ideal R) (hp : Prime p) : Prime (Ideal.map Φ.toRingHom p)`
- **What**: The image of a prime ideal under a ring isomorphism is prime.
- **How**: `Ideal.map_isPrime_of_equiv` gives `IsPrime`; nonzero is shown by pushing `⊥` back through
  `map_le_map_iff_ringEquiv` (which equates `map ≤ bot` with `p ≤ bot`).
- **Hypotheses**: `p` is a prime ideal; `Φ` is a ring iso.
- **Uses from project**: `map_le_map_iff_ringEquiv`
- **Used by**: `count_map_ringEquiv`
- **Visibility**: public
- **Lines**: 66–77, proof ~11 lines
- **Notes**: None

---

### `theorem map_ne_bot_ringEquiv`
- **Type**: `(Φ : R ≃+* R') (I : Ideal R) (hI : I ≠ ⊥) : Ideal.map Φ.toRingHom I ≠ ⊥`
- **What**: The image of a nonzero ideal under a ring isomorphism is nonzero.
- **How**: By contradiction: if `map I = ⊥` then `I ≤ ⊥` via `map_le_map_iff_ringEquiv`, hence `I = ⊥`.
- **Hypotheses**: `I ≠ ⊥`; `Φ` is a ring iso.
- **Uses from project**: `map_le_map_iff_ringEquiv`
- **Used by**: `count_map_ringEquiv`, `intValuation_map_ringEquiv`
- **Visibility**: public
- **Lines**: 80–86, proof ~7 lines
- **Notes**: None

---

### `theorem map_dvd_iff_ringEquiv`
- **Type**: `(Φ : R ≃+* R') (A B : Ideal R) : Ideal.map Φ A ∣ Ideal.map Φ B ↔ A ∣ B`
- **What**: Divisibility of ideals is preserved (in both directions) by a ring isomorphism.
- **How**: Both directions use `map_dvd` with `Ideal.mapHom`, with the forward direction using
  `Φ.symm` and simplifying via `Ideal.map_map` and `hcomp : Φ.symm ∘ Φ = id`.
- **Hypotheses**: `Φ` is a ring iso.
- **Uses from project**: none
- **Used by**: `pow_dvd_iff_map_ringEquiv`
- **Visibility**: public
- **Lines**: 88–99, proof ~11 lines
- **Notes**: None

---

### `theorem pow_dvd_iff_map_ringEquiv`
- **Type**: `(Φ : R ≃+* R') (p I : Ideal R) (n : ℕ) : Ideal.map Φ p ^ n ∣ Ideal.map Φ I ↔ p ^ n ∣ I`
- **What**: Prime-power divisibility of ideals transports under a ring isomorphism.
- **How**: Rewrites via `Ideal.map_pow` to reduce to `map_dvd_iff_ringEquiv`.
- **Hypotheses**: `Φ` is a ring iso.
- **Uses from project**: `map_dvd_iff_ringEquiv`
- **Used by**: `count_map_ringEquiv`
- **Visibility**: public
- **Lines**: 101–105, proof ~4 lines
- **Notes**: None

---

### `theorem count_map_ringEquiv`
- **Type**: `(Φ : R ≃+* R') (p I : Ideal R) (hp : Prime p) (hI : I ≠ ⊥) : (Associates.mk (map Φ p)).count (Associates.mk (map Φ I)).factors = (Associates.mk p).count (Associates.mk I).factors`
- **What**: The `Associates` multiplicity (`count`) of a prime in a factorization is preserved by the
  ideal-lattice isomorphism `Ideal.map Φ`.
- **How**: Characterizes both counts via the `n ≤ count ↔ p^n ∣ I` criterion
  (`Associates.prime_pow_dvd_iff_le`), then uses `pow_dvd_iff_map_ringEquiv` to equate the dvd
  conditions; concludes by antisymmetry (`le_antisymm`).
- **Hypotheses**: `p` prime, `I ≠ ⊥`, `Φ` ring iso.
- **Uses from project**: `map_prime_ringEquiv`, `map_ne_bot_ringEquiv`, `pow_dvd_iff_map_ringEquiv`
- **Used by**: `intValuation_map_ringEquiv`
- **Visibility**: public
- **Lines**: 107–133, proof ~27 lines
- **Notes**: `set_option maxHeartbeats 1000000` (line 107, NO-COMMENT). Uses `classical` for
  `Associates.count` decidability.

---

## Section `ValuationTransport`

### `theorem intValuation_map_ringEquiv`
- **Type**: `(Φ : R ≃+* R') (vP : HeightOneSpectrum R) (vQ : HeightOneSpectrum R') (hPQ : vQ.asIdeal = Ideal.map Φ vP.asIdeal) (r : R) : vQ.intValuation (Φ r) = vP.intValuation r`
- **What**: The integer adic valuation of `Φ r` at `vQ` equals the adic valuation of `r` at `vP`,
  when `vQ.asIdeal` is the image of `vP.asIdeal` under `Φ`.
- **How**: The zero case is immediate. For nonzero `r`, unfolds both sides via
  `HeightOneSpectrum.intValuation_if_neg`, rewrites the LHS span via
  `Ideal.map_span`/`Set.image_singleton`, then applies `count_map_ringEquiv` using primeness of
  `vP.asIdeal` and nonzero-ness of `span {r}`.
- **Hypotheses**: `vQ.asIdeal = Ideal.map Φ vP.asIdeal`; `Φ` is a ring iso; `vP`, `vQ` height-one primes.
- **Uses from project**: `count_map_ringEquiv`, `map_ne_bot_ringEquiv`
- **Used by**: `valuation_map_ringEquiv_algebraMap`
- **Visibility**: public
- **Lines**: 141–156, proof ~15 lines
- **Notes**: None

---

### `theorem valuation_map_ringEquiv_algebraMap`
- **Type**: `(Φ : R ≃+* R') (vP : ...) (vQ : ...) (hPQ : ...) (r : R) : vQ.valuation K' (ringEquivOfRingEquiv Φ (algebraMap R K r)) = vP.valuation K (algebraMap R K r)`
- **What**: The fraction-field adic valuation transports on elements of the form `algebraMap r`.
- **How**: Uses `IsFractionRing.ringEquivOfRingEquiv_algebraMap` to commute the fraction-ring equiv
  with `algebraMap`, then applies `HeightOneSpectrum.valuation_of_algebraMap` on both sides to
  reduce to `intValuation_map_ringEquiv`.
- **Hypotheses**: `K`, `K'` fraction fields of `R`, `R'`; `vQ.asIdeal = Ideal.map Φ vP.asIdeal`.
- **Uses from project**: `intValuation_map_ringEquiv`
- **Used by**: `valuation_map_ringEquiv`
- **Visibility**: public
- **Lines**: 159–167, proof ~8 lines
- **Notes**: None

---

### `theorem valuation_map_ringEquiv`
- **Type**: `(Φ : R ≃+* R') (vP : ...) (vQ : ...) (hPQ : ...) (f : K) : vQ.valuation K' (ringEquivOfRingEquiv Φ f) = vP.valuation K f`
- **What**: The main result: the fraction-field adic valuation transports under a ring isomorphism
  for ALL elements `f : K`, not just those in the image of `algebraMap`.
- **How**: Uses `IsFractionRing.div_surjective` to write `f = u/v` with `u, v : R`, then applies
  `map_div₀` and `Valuation.map_div` on both sides, reducing to `valuation_map_ringEquiv_algebraMap`
  applied twice (numerator and denominator).
- **Hypotheses**: `K`, `K'` fraction fields; `vQ.asIdeal = Ideal.map Φ vP.asIdeal`.
- **Uses from project**: `valuation_map_ringEquiv_algebraMap`
- **Used by**: unused in file (consumed by callers in `FrobeniusFunctionFieldEquiv.lean` etc.)
- **Visibility**: public
- **Lines**: 172–181, proof ~9 lines
- **Notes**: This is the key exported theorem — the divisor-Galois-descent engine.

---

## Geometric Ideal Transport (no section marker)

### `theorem map_XClass`
- **Type**: `(W' : WeierstrassCurve.Affine A) (f : A →+* B) (x : A) : CoordinateRing.map W' f (CoordinateRing.XClass W' x) = CoordinateRing.XClass (W'.map f).toAffine (f x)`
- **What**: `CoordinateRing.map f` sends the `XClass x` generator to `XClass (f x)` on the
  mapped curve.
- **How**: Unfolds `XClass` and `CoordinateRing.map_mk`, then `congr 1` reduces to checking
  `map_C` and `map_sub` for polynomials.
- **Hypotheses**: `f : A →+* B` is a ring homomorphism.
- **Uses from project**: none (pure mathlib)
- **Used by**: `map_XYIdeal`
- **Visibility**: public
- **Lines**: 188–196, proof ~8 lines
- **Notes**: None

---

### `theorem map_YClass`
- **Type**: `(W' : WeierstrassCurve.Affine A) (f : A →+* B) (y : A[X]) : CoordinateRing.map W' f (CoordinateRing.YClass W' y) = CoordinateRing.YClass (W'.map f).toAffine (y.map f)`
- **What**: `CoordinateRing.map f` sends `YClass y` to `YClass (y.map f)` on the mapped curve.
- **How**: Same pattern as `map_XClass`: unfold via `map_mk`, then `congr 1` + `map_sub`.
- **Hypotheses**: `f : A →+* B`.
- **Uses from project**: none
- **Used by**: `map_XYIdeal`
- **Visibility**: public
- **Lines**: 199–206, proof ~7 lines
- **Notes**: None

---

### `theorem map_XYIdeal`
- **Type**: `(W' : Affine A) (f : A →+* B) (x : A) (y : A[X]) : Ideal.map (CoordinateRing.map W' f) (CoordinateRing.XYIdeal W' x y) = CoordinateRing.XYIdeal (W'.map f).toAffine (f x) (y.map f)`
- **What**: `CoordinateRing.map f` sends the maximal ideal `XYIdeal(x,y)` at a point to the
  maximal ideal `XYIdeal(f(x), y.map f)` at the image point — the coordinate-ring shadow of
  "ring iso sends maximal ideal at P to maximal ideal at f(P)".
- **How**: Unfolds both `XYIdeal`s as spans, applies `Ideal.map_span` + `Set.image_insert_eq` +
  `Set.image_singleton`, then applies `map_XClass` and `map_YClass`.
- **Hypotheses**: `f : A →+* B`.
- **Uses from project**: `map_XClass`, `map_YClass`
- **Used by**: unused in file (consumed by callers in other files, e.g. `FrobeniusGaloisDescent`)
- **Visibility**: public
- **Lines**: 211–219, proof ~8 lines
- **Notes**: None

---

## Section: Cast lemmas (`RingEquiv.cast` transport)

### `theorem pointValuation_ringEquivCast`
- **Type**: `(V₁ V₂ : WeierstrassCurve F) (hV : V₁ = V₂) (P₁ : SmoothPoint V₁) (P₂ : SmoothPoint V₂) (hP : HEq P₁ P₂) (g : V₁.toAffine.FunctionField) : V₂.pointValuation P₂ (RingEquiv.cast hV g) = V₁.pointValuation P₁ g`
- **What**: The `pointValuation` of a function field element transports through the cast
  `RingEquiv.cast` induced by a curve equality `V₁ = V₂`, provided the points are heterogeneously equal.
- **How**: `subst hV` collapses the curve equality to `rfl`; `obtain rfl := eq_of_heq hP` makes
  `P₁ = P₂`; the goal becomes `rfl`.
- **Hypotheses**: `V₁ = V₂`; `HEq P₁ P₂`.
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 234–244, proof ~10 lines
- **Notes**: The `RingEquiv.cast` approach (rather than `▸`) is the key insight that avoids
  curve-indexed `Eq.rec` whnf-timeouts.

---

### `theorem ord_P_ringEquivCast`
- **Type**: `(V₁ V₂ : WeierstrassCurve F) (hV : V₁ = V₂) (P₁ : SmoothPoint V₁) (P₂ : SmoothPoint V₂) (hP : HEq P₁ P₂) (g : V₁.toAffine.FunctionField) : V₂.ord_P P₂ (RingEquiv.cast hV g) = V₁.ord_P P₁ g`
- **What**: The additive order `ord_P` transports through `RingEquiv.cast` (additive form of
  `pointValuation_ringEquivCast`).
- **How**: Same `subst hV; obtain rfl := eq_of_heq hP; rfl` pattern.
- **Hypotheses**: `V₁ = V₂`; `HEq P₁ P₂`.
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 248–258, proof ~10 lines
- **Notes**: None

---

### `theorem heq_smoothPoint`
- **Type**: `(W₁ W₂ : WeierstrassCurve.Affine F) (hW : W₁ = W₂) (P₁ : SmoothPoint W₁) (P₂ : SmoothPoint W₂) (hx : P₁.x = P₂.x) (hy : P₁.y = P₂.y) : HEq P₁ P₂`
- **What**: Two smooth points on equal affine curves with matching coordinates are
  heterogeneously equal.
- **How**: `subst hW` makes both on the same curve; `SmoothPlaneCurve.SmoothPoint.ext` gives
  `P₁ = P₂` from coordinate equality; `rw` finishes.
- **Hypotheses**: Equal curves, equal x- and y-coordinates.
- **Uses from project**: `HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.ext`
- **Used by**: unused in file (bookkeeping for callers using `pointValuation_ringEquivCast`)
- **Visibility**: public
- **Lines**: 263–272, proof ~9 lines
- **Notes**: None

---

### `theorem ordAtInfty_ringEquivCast`
- **Type**: `(V₁ V₂ : WeierstrassCurve F) (hV : V₁ = V₂) (g : V₁.toAffine.FunctionField) : V₂.ordAtInfty (RingEquiv.cast hV g) = V₁.ordAtInfty g`
- **What**: The order at infinity transports through `RingEquiv.cast` along a curve equality.
- **How**: `subst hV; rfl` — the cast collapses entirely.
- **Hypotheses**: `V₁ = V₂`.
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 276–283, proof ~7 lines
- **Notes**: Simplest of the cast lemmas — no point HEq needed for ∞.

---

## Summary table

| Name | Kind | Lines | Sorry | maxHB | Long (>30L) |
|------|------|-------|-------|-------|-------------|
| `map_le_map_iff_ringEquiv` | theorem | 56–63 | no | — | no |
| `map_prime_ringEquiv` | theorem | 66–77 | no | — | no |
| `map_ne_bot_ringEquiv` | theorem | 80–86 | no | — | no |
| `map_dvd_iff_ringEquiv` | theorem | 88–99 | no | — | no |
| `pow_dvd_iff_map_ringEquiv` | theorem | 101–105 | no | — | no |
| `count_map_ringEquiv` | theorem | 107–133 | no | 1000000 (line 107, no comment) | no (27L) |
| `intValuation_map_ringEquiv` | theorem | 141–156 | no | — | no |
| `valuation_map_ringEquiv_algebraMap` | theorem | 159–167 | no | — | no |
| `valuation_map_ringEquiv` | theorem | 172–181 | no | — | no |
| `map_XClass` | theorem | 188–196 | no | — | no |
| `map_YClass` | theorem | 199–206 | no | — | no |
| `map_XYIdeal` | theorem | 211–219 | no | — | no |
| `pointValuation_ringEquivCast` | theorem | 234–244 | no | — | no |
| `ord_P_ringEquivCast` | theorem | 248–258 | no | — | no |
| `heq_smoothPoint` | theorem | 263–272 | no | — | no |
| `ordAtInfty_ringEquivCast` | theorem | 276–283 | no | — | no |

**Total**: 16 declarations, all theorems, 0 sorry, 0 instances, 0 defs.
