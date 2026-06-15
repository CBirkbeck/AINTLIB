# Inventory: ./HasseWeil/AdditionPullback/SamePlace.lean

**Summary:** 47 declarations (1 abbrev, 46 theorems; all private except 16 public). No `sorry`, no `set_option maxHeartbeats`. This is the addition-formula analogue of `EC/MulByIntSamePlace.lean`, providing the **SamePlace** (`Valuation.IsEquiv`) input for the `1 − π` isogeny order-transport, plus a general-isogeny version keyed on generator residues.

---

## Section: Replicated value-bridge lemmas (private)

---

### `private theorem pV_aeval_sub_eval_lt_one`
- **Type**: `(P : SmoothPoint) → pointValuation P u ≤ 1 → pointValuation P (u − a) < 1 → (q : Polynomial F) → pointValuation P (aeval u q − algebraMap (q.eval a)) < 1`
- **What**: Univariate value bridge: if `u` is regular at `P` and `u ≡ a mod m_P`, then `q(u) ≡ q(a) mod m_P` for any polynomial `q`.
- **How**: Polynomial induction; the monomial step splits as `u·(q(u)−q(a)) + q(a)·(u−a)` and uses `pointValuation_mul_lt_one_of_le_and_lt` twice.
- **Hypotheses**: Smooth point `P`; `u` regular at `P`; `u ≡ a mod m_P`.
- **Uses from project**: `pointValuation_mul_lt_one_of_le_and_lt`, `SmoothPlaneCurve.pointValuation_algebraMap_F_le_one`.
- **Used by**: `pV_bivariate_bridge` (which calls it in the `C q` case), and (transitively) all residue-bridge consumers.
- **Visibility**: private
- **Lines**: 83–121, proof ~38 lines
- **Notes**: Verbatim copy of the same-named private lemma in `MulByIntSamePlace.lean`. Proof >30 lines.

---

### `private theorem pV_algebraMap_sub_evalAt_lt_one`
- **Type**: `(P : SmoothPoint) → (r : CoordinateRing) → pointValuation P (algebraMap r − evalAt P r) < 1`
- **What**: Coordinate-ring residue bridge: a coordinate-ring element `r` is congruent mod `m_P` to its evaluation `evalAt P r`.
- **How**: Uses `ker_evalAt` to show `r − algebraMap(evalAt P r) ∈ maximalIdealAt P`, then applies `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`.
- **Hypotheses**: Smooth point `P`; `r` a coordinate-ring element.
- **Uses from project**: `SmoothPlaneCurve.ker_evalAt`, `SmoothPlaneCurve.evalAt_algebraMap`, `Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`.
- **Used by**: `resid_y_gen`.
- **Visibility**: private
- **Lines**: 125–141, proof ~17 lines

---

### `private theorem pV_bivariate_bridge`
- **Type**: `(P : SmoothPoint) → u ≡ a, v ≡ b mod m_P (both regular) → (p : Polynomial (Polynomial F)) → pointValuation P (p(u,v) − p(a,b)) < 1`
- **What**: Bivariate value bridge: congruences mod `m_P` are preserved by any bivariate polynomial `p`.
- **How**: Polynomial induction; the monomial step splits `Au·v − Ab·b = Au·(v−b) + b·(Au−Ab)` and applies `pointValuation_mul_lt_one_of_le_and_lt` with `pV_aeval_sub_eval_lt_one` for the inner induction.
- **Hypotheses**: Smooth point `P`; `u ≡ a`, `v ≡ b` mod `m_P`, both regular.
- **Uses from project**: `pV_aeval_sub_eval_lt_one`, `pointValuation_add_le_one`, `pointValuation_mul_lt_one_of_le_and_lt`, `SmoothPlaneCurve.pointValuation_algebraMap_F_le_one`.
- **Used by**: `pV_addIsog_pullback_algebraMap_sub_evalAt_lt_one`, `pV_isog_pullback_algebraMap_sub_evalAt_lt_one`.
- **Visibility**: private
- **Lines**: 145–198, proof ~54 lines
- **Notes**: Verbatim copy from `MulByIntSamePlace.lean`. Proof >30 lines.

---

## Section: Residue toolkit (private)

---

### `private abbrev resid`
- **Type**: `(P : SmoothPoint) → (u : KE) → (a : F) → Prop`, defined as `pointValuation P (u − algebraMap a) < 1`
- **What**: Notation for "u is congruent to a mod m_P".
- **How**: Definition.
- **Hypotheses**: None.
- **Uses from project**: `SmoothPlaneCurve.pointValuation`.
- **Used by**: Every subsequent private and public theorem in the file.
- **Visibility**: private
- **Lines**: 209–210, 2 lines

---

### `private theorem resid_le_one`
- **Type**: `resid P u a → pointValuation P u ≤ 1`
- **What**: A residue `u ≡ a` makes `u` regular at `P`.
- **How**: Splits `u = (u−a) + a`, uses `pointValuation_add_le_one`.
- **Hypotheses**: `resid P u a`.
- **Uses from project**: `pointValuation_add_le_one`, `SmoothPlaneCurve.pointValuation_algebraMap_F_le_one`.
- **Used by**: `resid_mul`, `pV_addIsog_pullback_algebraMap_sub_evalAt_lt_one`, `pV_isog_pullback_algebraMap_sub_evalAt_lt_one`, `pV_bivariate_bridge` (via bridge calls).
- **Visibility**: private
- **Lines**: 213–217, proof 4 lines

---

### `private theorem resid_add`
- **Type**: `resid P u a → resid P v b → resid P (u + v) (a + b)`
- **What**: Residues add.
- **How**: Rewrites `(u+v)−(a+b) = (u−a)+(v−b)`, applies `map_add` bound + `max_lt`.
- **Hypotheses**: Two residue witnesses.
- **Uses from project**: `SmoothPlaneCurve.pointValuation` (via `map_add`).
- **Used by**: `resid_sq` (transitively via `resid_mul`), `resid_addPullback_x_pair`, `resid_addPullback_y_pair`, `resid_addPullback_x_pair_of_slope`, `resid_addPullback_y_pair_of_slope`.
- **Visibility**: private
- **Lines**: 220–226, proof 6 lines

---

### `private theorem resid_sub`
- **Type**: `resid P u a → resid P v b → resid P (u - v) (a - b)`
- **What**: Residues subtract.
- **How**: Rewrites `(u−v)−(a−b) = (u−a)−(v−b)`, applies `map_sub` + `max_lt`.
- **Hypotheses**: Two residue witnesses.
- **Uses from project**: None.
- **Used by**: `resid_div`, `resid_addSlopePair`, `resid_addPullback_x_pair`, `resid_addPullback_y_pair`, `resid_addPullback_x_pair_of_slope`, `resid_addPullback_y_pair_of_slope`.
- **Visibility**: private
- **Lines**: 229–235, proof 5 lines

---

### `private theorem resid_mul`
- **Type**: `resid P u a → resid P v b → resid P (u * v) (a * b)`
- **What**: Residues multiply.
- **How**: Splits `u·v − a·b = u·(v−b) + b·(u−a)`, applies `pointValuation_mul_lt_one_of_le_and_lt` twice with `resid_le_one` and `pointValuation_algebraMap_F_le_one`.
- **Hypotheses**: Two residue witnesses.
- **Uses from project**: `resid_le_one`, `pointValuation_mul_lt_one_of_le_and_lt`, `SmoothPlaneCurve.pointValuation_algebraMap_F_le_one`.
- **Used by**: `resid_sq`, `resid_pow`, `resid_div`, `resid_addSlopePair`, `resid_addPullback_x_pair`, `resid_addPullback_y_pair`, `resid_addPullback_x_pair_of_slope`, `resid_addPullback_y_pair_of_slope`.
- **Visibility**: private
- **Lines**: 238–249, proof 11 lines

---

### `private theorem resid_const`
- **Type**: `(P : SmoothPoint) → (c : F) → resid P (algebraMap F KE c) c`
- **What**: A constant `algebraMap c` residues to `c`.
- **How**: `sub_self` + `map_zero` + `zero_lt_one`.
- **Hypotheses**: None.
- **Uses from project**: None.
- **Used by**: `resid_div`, `resid_pow`, `resid_a₁`, `resid_addPullback_x_pair`, `resid_addPullback_y_pair`, `resid_addPullback_x_pair_of_slope`, `resid_addPullback_y_pair_of_slope`.
- **Visibility**: private
- **Lines**: 252–254, proof 2 lines

---

### `private theorem resid_unit`
- **Type**: `resid P u a → a ≠ 0 → pointValuation P u = 1`
- **What**: A residue `u ≡ a` with `a ≠ 0` forces `pV u = 1`.
- **How**: Uses `pointValuation_algebraMap_F_eq_one_of_ne_zero` for `a`, then `map_add_eq_of_lt_right`.
- **Hypotheses**: `resid P u a`, `a ≠ 0`.
- **Uses from project**: `pointValuation_algebraMap_F_eq_one_of_ne_zero`.
- **Used by**: `resid_div`, `resid_addSlopePair`.
- **Visibility**: private
- **Lines**: 257–264, proof 7 lines

---

### `private theorem resid_div`
- **Type**: `resid P u a → resid P d c → c ≠ 0 → resid P (u/d) (a/c)`
- **What**: Residues divide: `u ≡ a`, `d ≡ c` with `c ≠ 0` gives `u/d ≡ a/c`.
- **How**: Uses `resid_unit` to establish that `d` is a unit at `P` (nonzero); shows `u·c − a·d ≡ 0` via `resid_sub` + `resid_mul`; rewrites `u/d − a/c` as the numerator times the unit denominator inverse; applies `pointValuation_mul_lt_one_of_le_and_lt` with the unit bound `≤ 1`.
- **Hypotheses**: Three residue witnesses; `c ≠ 0`.
- **Uses from project**: `resid_unit`, `resid_sub`, `resid_mul`, `resid_const`, `pointValuation_algebraMap_F_eq_one_of_ne_zero`, `pointValuation_mul_lt_one_of_le_and_lt`.
- **Used by**: `resid_addSlopePair`.
- **Visibility**: private
- **Lines**: 268–297, proof ~30 lines

---

### `private theorem resid_sq`
- **Type**: `resid P u a → resid P (u^2) (a^2)`
- **What**: Residues square (derived from `resid_mul`).
- **How**: Rewrite `u^2 = u*u`, apply `resid_mul`.
- **Hypotheses**: `resid P u a`.
- **Uses from project**: `resid_mul`.
- **Used by**: `resid_addPullback_x_pair`, `resid_addPullback_y_pair`, `resid_addPullback_x_pair_of_slope`, `resid_addPullback_y_pair_of_slope`.
- **Visibility**: private
- **Lines**: 300–303, proof 3 lines

---

### `private theorem resid_pow`
- **Type**: `resid P u a → (n : ℕ) → resid P (u^n) (a^n)`
- **What**: Residues raise to a natural power (induction on `n`).
- **How**: `Nat.rec`; base `resid_const P 1`; step `resid_mul ih hu`.
- **Hypotheses**: `resid P u a`.
- **Uses from project**: `resid_const`, `resid_mul`.
- **Used by**: Not used in this file (available for external callers).
- **Visibility**: private
- **Lines**: 306–310, proof 4 lines

---

### `private theorem resid_x_gen`
- **Type**: `(P : SmoothPoint) → resid P (x_gen W) P.x`
- **What**: The generic `x`-coordinate residues to `P.x` mod `m_P`.
- **How**: Rewrites `x_gen − P.x = algebraMap (XClass)` via `x_gen_sub_const_eq_algebraMap_XClass`, then applies `XClass_mem_maximalIdealAt` + `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`.
- **Hypotheses**: Smooth point `P`.
- **Uses from project**: `x_gen_sub_const_eq_algebraMap_XClass`, `XClass_mem_maximalIdealAt`, `Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`.
- **Used by**: Used only within `resid_y_gen` (via `pV_algebraMap_sub_evalAt_lt_one`), and visible for external use.
- **Visibility**: private
- **Lines**: 313–318, proof 5 lines

---

### `private theorem resid_y_gen`
- **Type**: `(P : SmoothPoint) → resid P (y_gen W) P.y`
- **What**: The generic `y`-coordinate residues to `P.y` mod `m_P`.
- **How**: Instantiates `pV_algebraMap_sub_evalAt_lt_one` at `mk Polynomial.X`; recognises `mk Polynomial.X = y_gen` and `evalAt P (mk X) = P.y` via `Curves.SmoothPlaneCurve.evalAt_mk`.
- **Hypotheses**: Smooth point `P`.
- **Uses from project**: `pV_algebraMap_sub_evalAt_lt_one`, `Curves.SmoothPlaneCurve.evalAt_mk`.
- **Used by**: Not called within this file (base residue for external consumers).
- **Visibility**: private
- **Lines**: 321–331, proof 10 lines

---

### `private theorem resid_addSlopePair`
- **Type**: Four generator residues + `x₁ ≠ x₂` → `resid P (addSlopePair α₁ α₂) (slope x₁ x₂ y₁ y₂)`
- **What**: The `K(E)`-slope element `addSlopePair α₁ α₂` residues to the secant slope `(y₁−y₂)/(x₁−x₂)` when the two `x`-residues are distinct.
- **How**: Shows `α₁^*x − α₂^*x ≠ 0` in `K(E)` by the residue distinctness (via `resid_unit`); uses `addSlopePair_eq_of_x_ne`; applies `resid_div` + `resid_sub`.
- **Hypotheses**: Four generator residues; `x₁ ≠ x₂`.
- **Uses from project**: `resid_sub`, `resid_unit`, `resid_div`, `addSlopePair_eq_of_x_ne`, `WeierstrassCurve.Affine.slope_of_X_ne`.
- **Used by**: `resid_addPullback_x_pair`, `resid_addPullback_y_pair`.
- **Visibility**: private
- **Lines**: 349–370, proof ~22 lines

---

### `private theorem resid_a₁`
- **Type**: `(P : SmoothPoint) → resid P (algebraMap W.toAffine.a₁) W.toAffine.a₁`
- **What**: The Weierstrass coefficient `a₁` (as a `K(E)`-constant) residues to itself.
- **How**: Direct application of `resid_const`.
- **Hypotheses**: None beyond the global variable `W`.
- **Uses from project**: `resid_const`.
- **Used by**: `resid_addPullback_x_pair`, `resid_addPullback_y_pair`, `resid_addPullback_x_pair_of_slope`, `resid_addPullback_y_pair_of_slope`.
- **Visibility**: private
- **Lines**: 373–374, proof 1 line

---

### `private theorem resid_addPullback_x_pair`
- **Type**: Four generator residues + `x₁ ≠ x₂` → `resid P (addPullback_x_pair α₁ α₂) (addX x₁ x₂ (slope x₁ x₂ y₁ y₂))`
- **What**: The addition-formula `x`-coordinate `addPullback_x_pair` residues to `addX` of the residue values (secant case).
- **How**: Derives slope residue via `resid_addSlopePair`; unfolds `addPullback_x_pair` as `L² + a₁·L − a₂ − x₁ − x₂`; assembles from `resid_sq`, `resid_mul`, `resid_add`, `resid_sub`, `resid_const`.
- **Hypotheses**: Four generator residues; `x₁ ≠ x₂`.
- **Uses from project**: `resid_addSlopePair`, `resid_sq`, `resid_mul`, `resid_a₁`, `resid_add`, `resid_sub`, `resid_const`.
- **Used by**: `resid_addPullback_y_pair`, `oneSub_coords_at_affine`, `isog_coords_at_affine_of_decomp`.
- **Visibility**: private
- **Lines**: 379–401, proof ~22 lines

---

### `private theorem resid_addPullback_y_pair`
- **Type**: Four generator residues + `x₁ ≠ x₂` → `resid P (addPullback_y_pair α₁ α₂) (addY x₁ x₂ y₁ (slope x₁ x₂ y₁ y₂))`
- **What**: The addition-formula `y`-coordinate `addPullback_y_pair` residues to `addY` of the residue values (secant case).
- **How**: Uses `resid_addSlopePair` and `resid_addPullback_x_pair`; unfolds `addPullback_y_pair = negY(addX, slope·(addX−x₁)+y₁)` and assembles residues via the toolkit.
- **Hypotheses**: Four generator residues; `x₁ ≠ x₂`.
- **Uses from project**: `resid_addSlopePair`, `resid_addPullback_x_pair`, `resid_sub`, `resid_add`, `resid_mul`, `resid_const`, `resid_a₁`.
- **Used by**: `oneSub_coords_at_affine`, `isog_coords_at_affine_of_decomp`.
- **Visibility**: private
- **Lines**: 406–449, proof ~43 lines
- **Notes**: Proof >30 lines.

---

### `private theorem resid_addPullback_x_pair_of_slope`
- **Type**: `resid P (α₁^*x_gen) x₁` + `resid P (α₂^*x_gen) x₂` + `resid P (addSlopePair α₁ α₂) ℓ` → `resid P (addPullback_x_pair α₁ α₂) (addX x₁ x₂ ℓ)`
- **What**: Slope-parametric `x`-residue: given an external slope residue `ℓ` (covers doubling case), `addPullback_x_pair` residues to `addX x₁ x₂ ℓ`.
- **How**: Same arithmetic as `resid_addPullback_x_pair` but without deriving the slope internally.
- **Hypotheses**: Two `x`-generator residues; slope residue.
- **Uses from project**: `resid_sq`, `resid_mul`, `resid_a₁`, `resid_add`, `resid_sub`, `resid_const`.
- **Used by**: `resid_addPullback_y_pair_of_slope`, `isog_coords_at_affine_of_decomp_slope`.
- **Visibility**: private
- **Lines**: 464–480, proof ~17 lines

---

### `private theorem resid_addPullback_y_pair_of_slope`
- **Type**: Two `x`-generator residues + `resid P (α₁^*y_gen) y₁` + slope residue → `resid P (addPullback_y_pair α₁ α₂) (addY x₁ x₂ y₁ ℓ)`
- **What**: Slope-parametric `y`-residue (covers doubling case).
- **How**: Uses `resid_addPullback_x_pair_of_slope` for `addX`, then assembles `addY` residue from the slope and x residues.
- **Hypotheses**: Two `x`-generator residues; `y₁`-residue; slope residue.
- **Uses from project**: `resid_addPullback_x_pair_of_slope`, `resid_sub`, `resid_add`, `resid_mul`, `resid_const`, `resid_a₁`.
- **Used by**: `isog_coords_at_affine_of_decomp_slope`.
- **Visibility**: private
- **Lines**: 485–519, proof ~34 lines
- **Notes**: Proof >30 lines.

---

## Section: Centerpiece

---

### `theorem oneSub_coords_at_affine`
- **Type**: Given `AddNonInversePair`, injective `addCoordAlgHomPair`, smooth point `P`, images `α₁(P) = some x₁ y₁`, `α₂(P) = some x₂ y₂`, four generator residues, `x₁ ≠ x₂`, image `(addIsog)(P) = some x y`: `resid P (addPullback_x_pair α₁ α₂) x ∧ resid P (addPullback_y_pair α₁ α₂) y`
- **What**: The addition-formula closed-point specialisation: the addition-formula comorphism coordinates residue to the image coordinates at an affine image in the non-doubling case. This is the `1−π` analogue of `mulByInt_coords_at_affine`.
- **How**: Uses mathlib `Affine.Point.add_some` to identify the image coordinates with `addX x₁ x₂ (slope ..)` and `addY x₁ x₂ y₁ (slope ..)`; then applies `resid_addPullback_x_pair` and `resid_addPullback_y_pair`.
- **Hypotheses**: `AddNonInversePair α₁ α₂`; injective `addCoordAlgHomPair`; both summand images affine; four per-summand generator residues; non-doubling `x₁ ≠ x₂`; image affine.
- **Uses from project**: `addIsog_toAddMonoidHom`, `resid_addPullback_x_pair`, `resid_addPullback_y_pair`.
- **Used by**: Not called in this file; used in `OneSubAffineResidues.lean`, `OneSubComapConcrete.lean`.
- **Visibility**: public
- **Lines**: 535–563, proof ~29 lines

---

## Section: Transfer (addIsog-keyed)

---

### `private theorem addIsog_pullback_algebraMap_mk_eq`
- **Type**: `(p : Polynomial (Polynomial F)) → (addIsog hxy hinj).pullback (algebraMap (mk p)) = (p.map (algebraMap)).evalEval (addPullback_x_pair α₁ α₂) (addPullback_y_pair α₁ α₂)`
- **What**: The `addIsog` comorphism on `algebraMap (mk p)` equals bivariate polynomial evaluation at the addition-formula coordinate functions.
- **How**: Uses `addIsog_pullback`, unfolds `addPullbackAlgHomPair` + `addCoordRingHomPair`, uses `IsFractionRing.liftAlgHom_apply`, `AdjoinRoot.lift_mk`, `Polynomial.eval₂_eval₂RingHom_apply`.
- **Hypotheses**: `AddNonInversePair`, injective `addCoordAlgHomPair`.
- **Uses from project**: `addIsog_pullback`, `addPullbackAlgHomPair`, `addCoordRingHomPair`.
- **Used by**: `pV_addIsog_pullback_algebraMap_sub_evalAt_lt_one`.
- **Visibility**: private
- **Lines**: 582–596, proof ~14 lines

---

### `private theorem pV_addIsog_pullback_algebraMap_sub_evalAt_lt_one`
- **Type**: Given coordinate residues `hx`, `hy` and `r : CoordinateRing`: `pV P ((addIsog).pullback (algebraMap r) − evalAt ⟨x,y,h_ns⟩ r) < 1`
- **What**: Residue matching for coordinate-ring elements through `addIsog`'s comorphism: the pullback residues to the evaluation at the image point.
- **How**: Surjectivity of `AdjoinRoot.mk` to decompose `r`; uses `addIsog_pullback_algebraMap_mk_eq` to identify the pullback with a bivariate evalEval; applies `pV_bivariate_bridge` with the coordinate residues `hx`, `hy`.
- **Hypotheses**: Coordinate residues `hx`, `hy`; coordinate-ring element `r`.
- **Uses from project**: `addIsog_pullback_algebraMap_mk_eq`, `pV_bivariate_bridge`, `resid_le_one`, `Curves.SmoothPlaneCurve.evalAt_mk`.
- **Used by**: `pV_addIsog_pullback_algebraMap_le_one`, `pV_addIsog_pullback_algebraMap_eq_one_of_notMem`, `pV_addIsog_pullback_algebraMap_lt_one_of_mem`.
- **Visibility**: private
- **Lines**: 602–615, proof ~13 lines

---

### `private theorem pV_addIsog_pullback_algebraMap_le_one`
- **Type**: Coordinate residues + `r : CoordinateRing` → `pV P ((addIsog).pullback (algebraMap r)) ≤ 1`
- **What**: Regularity: the `addIsog`-pullback of any coordinate-ring element is regular at `P`.
- **How**: Rewrites pullback as `(diff) + (evalAt)`, applies `pointValuation_add_le_one` with `pV_addIsog_pullback_algebraMap_sub_evalAt_lt_one` and `pointValuation_algebraMap_F_le_one`.
- **Hypotheses**: Coordinate residues.
- **Uses from project**: `pV_addIsog_pullback_algebraMap_sub_evalAt_lt_one`, `pointValuation_add_le_one`, `SmoothPlaneCurve.pointValuation_algebraMap_F_le_one`.
- **Used by**: `pV_addIsog_pullback_le_one_of_le_one`.
- **Visibility**: private
- **Lines**: 618–635, proof ~17 lines

---

### `private theorem pV_addIsog_pullback_algebraMap_eq_one_of_notMem`
- **Type**: Coordinate residues + `r ∉ maximalIdealAt ⟨x,y,h_ns⟩` → `pV P ((addIsog).pullback (algebraMap r)) = 1`
- **What**: Unit transfer: if `r` is not in `m_Q`, then its pullback through `addIsog` is a unit at `P`.
- **How**: Uses `ker_evalAt` to get nonzero evaluation; `pointValuation_algebraMap_F_eq_one_of_ne_zero`; writes pullback as `diff + evalAt`, applies `map_add_eq_of_lt_right`.
- **Hypotheses**: Coordinate residues; `r ∉ m_Q`.
- **Uses from project**: `pV_addIsog_pullback_algebraMap_sub_evalAt_lt_one`, `pointValuation_algebraMap_F_eq_one_of_ne_zero`, `SmoothPlaneCurve.ker_evalAt`.
- **Used by**: `pV_addIsog_pullback_le_one_of_le_one`, `pV_addIsog_pullback_lt_one_of_lt_one`.
- **Visibility**: private
- **Lines**: 638–662, proof ~24 lines

---

### `private theorem pV_addIsog_pullback_algebraMap_lt_one_of_mem`
- **Type**: Coordinate residues + `r ∈ maximalIdealAt ⟨x,y,h_ns⟩` → `pV P ((addIsog).pullback (algebraMap r)) < 1`
- **What**: Vanishing transfer: if `r ∈ m_Q`, then its pullback is in `m_P`.
- **How**: Evaluates via `ker_evalAt`; applies `pV_addIsog_pullback_algebraMap_sub_evalAt_lt_one` at zero.
- **Hypotheses**: Coordinate residues; `r ∈ m_Q`.
- **Uses from project**: `pV_addIsog_pullback_algebraMap_sub_evalAt_lt_one`, `SmoothPlaneCurve.ker_evalAt`.
- **Used by**: `pV_addIsog_pullback_lt_one_of_lt_one`.
- **Visibility**: private
- **Lines**: 665–678, proof ~13 lines

---

### `private theorem pV_addIsog_pullback_le_one_of_le_one`
- **Type**: Coordinate residues + `pV ⟨x,y,h_ns⟩ g ≤ 1` → `pV P ((addIsog).pullback g) ≤ 1`
- **What**: Forward regularity transfer: if `g` is regular at the affine image, so is its pullback at `P`.
- **How**: Decomposes `g = u/v` with `v ∉ m_Q` using `IsLocalization.surj`; uses `pV_addIsog_pullback_algebraMap_eq_one_of_notMem` for `v`, `pV_addIsog_pullback_algebraMap_le_one` for `u`.
- **Hypotheses**: Coordinate residues; `g` regular at image.
- **Uses from project**: `pV_addIsog_pullback_algebraMap_eq_one_of_notMem`, `pV_addIsog_pullback_algebraMap_le_one`, `SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one`, `SmoothPlaneCurve.maximalIdealAt_isMaximal`.
- **Used by**: `addIsog_samePlace_le_one_iff_affine`.
- **Visibility**: private
- **Lines**: 683–714, proof ~32 lines
- **Notes**: Proof >30 lines.

---

### `private theorem pV_addIsog_pullback_lt_one_of_lt_one`
- **Type**: Coordinate residues + `pV ⟨x,y,h_ns⟩ g < 1` → `pV P ((addIsog).pullback g) < 1`
- **What**: Forward vanishing transfer: if `g` is in `m_Q`, so is its pullback at `P`.
- **How**: Same `IsLocalization.surj` decomposition; identifies `u ∈ m_Q` by comparing `pV` using `hv_unitQ`; applies vanishing transfer.
- **Hypotheses**: Coordinate residues; `g ∈ m_Q`.
- **Uses from project**: `pV_addIsog_pullback_algebraMap_eq_one_of_notMem`, `pV_addIsog_pullback_algebraMap_lt_one_of_mem`, `SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one`, `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`, `SmoothPlaneCurve.maximalIdealAt_isMaximal`.
- **Used by**: `addIsog_samePlace_le_one_iff_affine`.
- **Visibility**: private
- **Lines**: 717–761, proof ~44 lines
- **Notes**: Proof >30 lines.

---

### `theorem addIsog_samePlace_le_one_iff_affine`
- **Type**: Coordinate residues → `pV P ((addIsog).pullback g) ≤ 1 ↔ pV ⟨x,y,h_ns⟩ g ≤ 1`
- **What**: The affine SamePlace transfer for `addIsog`: regularity at `P` iff regularity at the image `⟨x,y,h_ns⟩`.
- **How**: Forward direction from `pV_addIsog_pullback_le_one_of_le_one`; backward direction by contrapositive via `g⁻¹` argument using `pV_addIsog_pullback_lt_one_of_lt_one`.
- **Hypotheses**: Coordinate residues.
- **Uses from project**: `pV_addIsog_pullback_le_one_of_le_one`, `pV_addIsog_pullback_lt_one_of_lt_one`.
- **Used by**: `addIsog_comap_pointValuation_isEquiv_affine`.
- **Visibility**: public
- **Lines**: 770–801, proof ~32 lines
- **Notes**: Proof >30 lines.

---

### `theorem addIsog_comap_pointValuation_isEquiv_affine`
- **Type**: Coordinate residues → `(pV P).comap (addIsog hxy hinj).pullback.toRingHom` IsEquiv `pV ⟨x,y,h_ns⟩`
- **What**: The comap valuation is `Valuation.IsEquiv` to the point valuation at the affine image.
- **How**: Applies `Valuation.isEquiv_of_val_le_one` reduced to the iff `addIsog_samePlace_le_one_iff_affine`.
- **Hypotheses**: Coordinate residues.
- **Uses from project**: `addIsog_samePlace_le_one_iff_affine`.
- **Used by**: `comap_pointValuation_addIsog_eq_affine_of_e_eq_one`.
- **Visibility**: public
- **Lines**: 807–818, proof ~11 lines

---

### `theorem comap_pointValuation_addIsog_eq_affine_of_e_eq_one`
- **Type**: Coordinate residues + `he1 : ord_P P ((addIsog).pullback (x_gen − x)) = 1` → `(pV P).comap (addIsog).pullback.toRingHom = pV ⟨x,y,h_ns⟩`
- **What**: Assembled affine comap identity for `addIsog`, carrying the `e = 1` uniformizer datum explicitly.
- **How**: One-line application of `Curves.SmoothPlaneCurve.comap_pointValuation_eq_of_isEquiv_of_ord_eq_one` with `addIsog_comap_pointValuation_isEquiv_affine` and the surjectivity fact.
- **Hypotheses**: Coordinate residues; `e = 1` datum `he1`.
- **Uses from project**: `addIsog_comap_pointValuation_isEquiv_affine`, `Curves.SmoothPlaneCurve.comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`, `SmoothPlaneCurve.pointValuation_surjective'`.
- **Used by**: Not called in this file. Appears unused in the project (superseded by the general version).
- **Visibility**: public
- **Lines**: 834–848, proof ~15 lines

---

## Section: IsogGeneral

---

### `theorem isog_coords_at_affine_of_decomp`
- **Type**: Given `hpb_x : α.pullback x_gen = addPullback_x_pair α₁ α₂`, `hpb_y`, summand images, four per-summand residues, `x₁ ≠ x₂`, `hsum_pt` (α(P) = α₁(P)+α₂(P)), `hQ` (α(P) = some x y): `resid P (α.pullback x_gen) x ∧ resid P (α.pullback y_gen) y`
- **What**: General isogeny closed-point residue production from an addition decomposition (non-doubling case): if an abstract isogeny `α`'s generator pullbacks equal those of an `addIsog`, and `α(P)` is the sum of the summand images, then `α`'s generator pullbacks residue to the image coordinates.
- **How**: Uses `Affine.Point.add_some` to identify image coordinates; applies `resid_addPullback_x_pair`/`_y_pair` after rewriting by `hpb_x`/`hpb_y`.
- **Hypotheses**: Pullback equality witnesses; all summand images affine; four per-summand residues; `x₁ ≠ x₂`; sum and image equalities.
- **Uses from project**: `resid_addPullback_x_pair`, `resid_addPullback_y_pair`.
- **Used by**: Not called in this file; used in `OneSubAffineResidues.lean`, `PencilComapWitnesses.lean`.
- **Visibility**: public
- **Lines**: 877–901, proof ~25 lines

---

### `theorem isog_coords_at_affine_of_decomp_slope`
- **Type**: Same as `isog_coords_at_affine_of_decomp` but with `hL : resid P (addSlopePair α₁ α₂) (slope x₁ x₂ y₁ y₂)` in place of `x₁ ≠ x₂`, and `hxy_pts : ¬(x₁ = x₂ ∧ y₁ = negY x₂ y₂)` in place of the strict inequality.
- **What**: Slope-parametric version covering the doubling case (`x₁ = x₂`): takes the slope residue as an explicit hypothesis.
- **How**: Same structure as `isog_coords_at_affine_of_decomp`; applies `resid_addPullback_x_pair_of_slope`/`_y_pair_of_slope`.
- **Hypotheses**: Pullback equality witnesses; summand images affine; `x`-residues for both, `y₁`-residue, slope residue; non-inverse condition; sum and image equalities.
- **Uses from project**: `resid_addPullback_x_pair_of_slope`, `resid_addPullback_y_pair_of_slope`.
- **Used by**: Not called in this file; used in `OneSubAffineResidues.lean`, `PencilComapWitnesses.lean`.
- **Visibility**: public
- **Lines**: 910–933, proof ~24 lines

---

### `theorem isog_pullback_algebraMap_mk_eq`
- **Type**: `(p : Polynomial (Polynomial F)) → α.pullback (algebraMap (mk p)) = (p.map (algebraMap)).evalEval (α.pullback x_gen) (α.pullback y_gen)`
- **What**: General isogeny-agnostic version of `addIsog_pullback_algebraMap_mk_eq`: the pullback of `algebraMap (mk p)` through any isogeny equals bivariate evaluation at the generator pullbacks.
- **How**: Rewrites using `evalEval_xy_gen_eq_algebraMap_mk`; uses `Polynomial.map_mapRingHom_evalEval` after verifying the compatibility `α.pullback.comp (algebraMap F KE) = algebraMap F KE` via `α.pullback.comp_algebraMap`.
- **Hypotheses**: None beyond the variable `α`.
- **Uses from project**: `evalEval_xy_gen_eq_algebraMap_mk`, `Polynomial.map_mapRingHom_evalEval`.
- **Used by**: `pV_isog_pullback_algebraMap_sub_evalAt_lt_one`.
- **Visibility**: public
- **Lines**: 940–956, proof ~16 lines

---

### `private theorem pV_isog_pullback_algebraMap_sub_evalAt_lt_one`
- **Type**: Generator residues + `r : CoordinateRing` → `pV P (α.pullback (algebraMap r) − evalAt ⟨x,y,h_ns⟩ r) < 1`
- **What**: General isogeny analogue of `pV_addIsog_pullback_algebraMap_sub_evalAt_lt_one`.
- **How**: Uses `isog_pullback_algebraMap_mk_eq` + `pV_bivariate_bridge`.
- **Hypotheses**: Generator residues.
- **Uses from project**: `isog_pullback_algebraMap_mk_eq`, `pV_bivariate_bridge`, `resid_le_one`, `Curves.SmoothPlaneCurve.evalAt_mk`.
- **Used by**: `pV_isog_pullback_algebraMap_le_one`, `pV_isog_pullback_algebraMap_eq_one_of_notMem`, `pV_isog_pullback_algebraMap_lt_one_of_mem`.
- **Visibility**: private
- **Lines**: 962–974, proof ~12 lines

---

### `private theorem pV_isog_pullback_algebraMap_le_one`
- **Type**: Generator residues + `r` → `pV P (α.pullback (algebraMap r)) ≤ 1`
- **What**: General isogeny regularity for coordinate-ring elements.
- **How**: Same as `pV_addIsog_pullback_algebraMap_le_one` using `pV_isog_pullback_algebraMap_sub_evalAt_lt_one`.
- **Hypotheses**: Generator residues.
- **Uses from project**: `pV_isog_pullback_algebraMap_sub_evalAt_lt_one`, `pointValuation_add_le_one`.
- **Used by**: `pV_isog_pullback_le_one_of_le_one`.
- **Visibility**: private
- **Lines**: 977–990, proof ~13 lines

---

### `private theorem pV_isog_pullback_algebraMap_eq_one_of_notMem`
- **Type**: Generator residues + `r ∉ m_Q` → `pV P (α.pullback (algebraMap r)) = 1`
- **What**: General isogeny unit transfer.
- **How**: Analogous to `pV_addIsog_pullback_algebraMap_eq_one_of_notMem`.
- **Hypotheses**: Generator residues; `r ∉ m_Q`.
- **Uses from project**: `pV_isog_pullback_algebraMap_sub_evalAt_lt_one`, `pointValuation_algebraMap_F_eq_one_of_ne_zero`.
- **Used by**: `pV_isog_pullback_le_one_of_le_one`, `pV_isog_pullback_lt_one_of_lt_one`.
- **Visibility**: private
- **Lines**: 993–1013, proof ~21 lines

---

### `private theorem pV_isog_pullback_algebraMap_lt_one_of_mem`
- **Type**: Generator residues + `r ∈ m_Q` → `pV P (α.pullback (algebraMap r)) < 1`
- **What**: General isogeny vanishing transfer.
- **How**: Analogous to `pV_addIsog_pullback_algebraMap_lt_one_of_mem`.
- **Hypotheses**: Generator residues; `r ∈ m_Q`.
- **Uses from project**: `pV_isog_pullback_algebraMap_sub_evalAt_lt_one`.
- **Used by**: `pV_isog_pullback_lt_one_of_lt_one`.
- **Visibility**: private
- **Lines**: 1016–1027, proof ~12 lines

---

### `private theorem pV_isog_pullback_le_one_of_le_one`
- **Type**: Generator residues + `pV ⟨x,y,h_ns⟩ g ≤ 1` → `pV P (α.pullback g) ≤ 1`
- **What**: General isogeny forward regularity transfer.
- **How**: Analogous to `pV_addIsog_pullback_le_one_of_le_one`.
- **Hypotheses**: Generator residues; `g` regular at image.
- **Uses from project**: `pV_isog_pullback_algebraMap_eq_one_of_notMem`, `pV_isog_pullback_algebraMap_le_one`.
- **Used by**: `isog_samePlace_le_one_iff_affine`.
- **Visibility**: private
- **Lines**: 1031–1061, proof ~31 lines
- **Notes**: Proof >30 lines.

---

### `private theorem pV_isog_pullback_lt_one_of_lt_one`
- **Type**: Generator residues + `pV ⟨x,y,h_ns⟩ g < 1` → `pV P (α.pullback g) < 1`
- **What**: General isogeny forward vanishing transfer.
- **How**: Analogous to `pV_addIsog_pullback_lt_one_of_lt_one`.
- **Hypotheses**: Generator residues; `g ∈ m_Q`.
- **Uses from project**: `pV_isog_pullback_algebraMap_eq_one_of_notMem`, `pV_isog_pullback_algebraMap_lt_one_of_mem`.
- **Used by**: `isog_samePlace_le_one_of_le_one` (via contrapositive in `isog_samePlace_le_one_iff_affine`).
- **Visibility**: private
- **Lines**: 1064–1107, proof ~44 lines
- **Notes**: Proof >30 lines.

---

### `theorem isog_samePlace_le_one_iff_affine`
- **Type**: Generator residues → `pV P (α.pullback g) ≤ 1 ↔ pV ⟨x,y,h_ns⟩ g ≤ 1`
- **What**: General isogeny SamePlace transfer: regularity at `P` iff at the affine image.
- **How**: Forward from `pV_isog_pullback_le_one_of_le_one`; backward by contrapositive via `g⁻¹` using `pV_isog_pullback_lt_one_of_lt_one`.
- **Hypotheses**: Generator residues.
- **Uses from project**: `pV_isog_pullback_le_one_of_le_one`, `pV_isog_pullback_lt_one_of_lt_one`.
- **Used by**: `isog_comap_pointValuation_isEquiv_affine`.
- **Visibility**: public
- **Lines**: 1112–1140, proof ~29 lines

---

### `theorem isog_comap_pointValuation_isEquiv_affine`
- **Type**: Generator residues → `(pV P).comap α.pullback.toRingHom` IsEquiv `pV ⟨x,y,h_ns⟩`
- **What**: General isogeny SamePlace IsEquiv.
- **How**: Applies `Valuation.isEquiv_of_val_le_one` reduced to `isog_samePlace_le_one_iff_affine`.
- **Hypotheses**: Generator residues.
- **Uses from project**: `isog_samePlace_le_one_iff_affine`.
- **Used by**: `comap_pointValuation_isog_eq_affine`, `comap_pointValuation_isog_eq_affine_y`.
- **Visibility**: public
- **Lines**: 1145–1155, proof ~10 lines

---

### `theorem ord_P_isog_pullback_x_sub_const_eq_one`
- **Type**: `omegaPullbackCoeff W α ∈ range`, `≠ 0`, `P` smooth, `resid P (α^*x_gen) x`, `ord_P P (alpha_star_u W α) = 0` → `ord_P P (α^*x_gen − x) = 1`
- **What**: General `e = 1` for the `x`-uniformizer: if `α` is separable (`a_α ≠ 0`) and its pullback of the 2-torsion-denominator `u` is a unit at `P`, then `α^*(x_gen − x)` has exact order 1 at `P`.
- **How**: Proves nonzero via `Dω_isog_pullback_x_gen` + `alpha_star_u` unit; `ord_P ≥ 1` from the residue (lies in `m_P`) via `one_le_ord_P_iff_pointValuation_lt_one`; `ord_P ≤ 1` from `ord_P_isog_pullback_x_sub_const_le_one` (DifferentialOrd.lean); antisymmetry.
- **Hypotheses**: Separability `a_α ≠ 0` (and range); `x`-residue; `alpha_star_u` a unit at `P`.
- **Uses from project**: `Dω_isog_pullback_x_gen`, `Dω_algebraMap`, `alpha_star_u`, `SmoothPlaneCurve.ord_P_zero`, `SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one`, `ord_P_isog_pullback_x_sub_const_le_one`.
- **Used by**: `comap_pointValuation_isog_eq_affine`.
- **Visibility**: public
- **Lines**: 1169–1201, proof ~33 lines
- **Notes**: Proof >30 lines.

---

### `theorem comap_pointValuation_isog_eq_affine`
- **Type**: `omegaPullbackCoeff W α` separable + range, generator residues, `alpha_star_u` unit at `P` → `(pV P).comap α.pullback.toRingHom = pV ⟨x,y,h_ns⟩`
- **What**: Assembled affine comap identity for a general isogeny with `e = 1` derived (no `he1` hypothesis).
- **How**: Applies `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one` with `isog_comap_pointValuation_isEquiv_affine` and `ord_P_isog_pullback_x_sub_const_eq_one`.
- **Hypotheses**: Separable coefficient; generator residues; `alpha_star_u` unit at `P` (non-2-torsion image).
- **Uses from project**: `isog_comap_pointValuation_isEquiv_affine`, `ord_P_isog_pullback_x_sub_const_eq_one`, `Curves.SmoothPlaneCurve.comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`, `SmoothPlaneCurve.pointValuation_surjective'`.
- **Used by**: Not called in this file; used extensively in `OneSubAffineResidues.lean`, `OneSubComapConcrete.lean`, `PencilComapWitnesses.lean`.
- **Visibility**: public
- **Lines**: 1211–1231, proof ~21 lines

---

### `theorem ord_P_isog_pullback_y_sub_const_eq_one`
- **Type**: Separable coefficient + range, `resid P (α^*y_gen) y`, `ord_P P (3*(α^*x_gen)^2+...) = 0` → `ord_P P (α^*y_gen − y) = 1`
- **What**: General `e = 1` for the `y`-uniformizer: if the pulled-back `y`-numerator `α^*ν` is a unit at `P` (2-torsion image case), then `α^*(y_gen − y)` has exact order 1.
- **How**: Proves nonzero via `Dω_isog_pullback_y_gen` + the nonzero numerator; `ord_P ≥ 1` from `y`-residue; `ord_P ≤ 1` from `ord_P_isog_pullback_y_sub_const_le_one`; antisymmetry.
- **Hypotheses**: Separable coefficient; `y`-residue; `y`-numerator unit at `P`.
- **Uses from project**: `Dω_isog_pullback_y_gen`, `Dω_algebraMap`, `SmoothPlaneCurve.ord_P_zero`, `SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one`, `ord_P_isog_pullback_y_sub_const_le_one`.
- **Used by**: `comap_pointValuation_isog_eq_affine_y`.
- **Visibility**: public
- **Lines**: 1244–1281, proof ~38 lines
- **Notes**: Proof >30 lines.

---

### `theorem comap_pointValuation_isog_eq_affine_y`
- **Type**: Separable coefficient, generator residues, `y`-numerator unit at `P` → `(pV P).comap α.pullback.toRingHom = pV ⟨x,y,h_ns⟩`
- **What**: Assembled affine comap identity via the `y`-uniformizer (2-torsion image case), `e = 1` derived.
- **How**: Applies `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one` with `isog_comap_pointValuation_isEquiv_affine` and `ord_P_isog_pullback_y_sub_const_eq_one`.
- **Hypotheses**: Separable coefficient; generator residues; `y`-numerator unit at `P`.
- **Uses from project**: `isog_comap_pointValuation_isEquiv_affine`, `ord_P_isog_pullback_y_sub_const_eq_one`, `Curves.SmoothPlaneCurve.comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`, `SmoothPlaneCurve.pointValuation_surjective'`.
- **Used by**: Not called in this file; used in `OneSubAffineResidues.lean`, `PencilComapWitnesses.lean`.
- **Visibility**: public
- **Lines**: 1291–1313, proof ~23 lines
