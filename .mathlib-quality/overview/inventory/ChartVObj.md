# Inventory — `projects/AdicSpaces/Adic spaces/FarguesFontaine/ChartVObj.lean`

File length: 1338 lines. Namespace `FarguesFontaine`.
Opens: `TopologicalRing ValuationSpectrum WittVector NNReal`.
File-level options: `set_option linter.overlappingInstances false` (line 28); whole file inside
`noncomputable section`.

Ambient variables (shared by every declaration):
`(p : ℕ) [Fact p.Prime]`, `(F : Type*)` a perfectoid field of characteristic `p` with its
topological/uniform/nonarchimedean structure, `(ϖ : PseudoUniformizer F)`, and implicit radii
`{ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}`.

Mathematical setting: `A_inf = W(O_F)`, `Bloc = A_inf[1/(p[ϖ])]`, the Fargues–Fontaine curve's
ambient space `𝒴`, its Big-window charts `chartData p F ϖ 1 b a b` (Kedlaya's `R(T/s)` with
`s = p[ϖ]^b`, `T = {p^{a+1}, [ϖ]^{b+1}}`), the closed-annulus ring `B^I ⊆ hatK_{ρ₁} × hatK_{ρ₂}`
(`BISub`) with its unit ball `BIPlusIn` (`wI ≤ 1`), and the ID2 comparison isomorphism
`presheafChartRingEquivBISub : O(U_{a,b}) ≃+* B^I`.

---

### `def chartPlus`

- **Type**:
  `chartPlus (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 : perfectoidValuation p F ϖ = ρ₁) (hexact2 : ρ₂ ^ a = perfectoidValuation p F ϖ ^ b) : ValuationSpectrum.PlusSubring (presheafValue (chartData p F ϖ 1 b a b))`
- **What**: Equips the chart's presheaf value (the completed rational localization `O(U_{a,b})`)
  with a plus subring, namely the transport of the `B^I`-unit ball `BIPlusIn` back along the ID2
  comparison isomorphism.
- **How**: Wraps `(BIPlusIn …).map e.symm.toRingHom` in the one-field `PlusSubring` structure, where
  `e = presheafChartRingEquivBISub`; pushforward of a subring along the inverse comparison ring hom.
- **Hypotheses**: `0 < a`, `0 < b`, `b ≤ a` (window shape), plus the two exactness conditions
  `|ϖ| = ρ₁` and `ρ₂^a = |ϖ|^b` identifying the annulus endpoints with the chart's rational window.
- **Uses from project**: `BIPlusIn`, `presheafChartRingEquivBISub`, `presheafValue`, `chartData`,
  `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`, `ValuationSpectrum.PlusSubring`.
- **Used by**: `chartVObj` (as the `letI` plus structure), `chartPlus_eq_canonical` (statement).
- **Visibility**: public
- **Lines**: 43–52 (definition body 4 lines)
- **Notes**: `noncomputable`. No `sorry`, no per-declaration `set_option`.

---

### `def chartTate`

- **Type**:
  `chartTate (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 …) (hexact2 …) : IsTateRing (presheafValue (chartData p F ϖ 1 b a b))`
- **What**: The chart value is a Tate ring — it has a pair of definition and a topologically
  nilpotent unit — because `B^I` is Tate and the comparison map is bicontinuous.
- **How**: Direct application of the project's transport lemma `isTateRing_congr` to
  `presheafChartRingEquivBISub …|>.symm`, feeding it the two continuity facts
  `presheafChartRingEquivBISub_symm_continuous` and `presheafChartRingEquivBISub_continuous`.
- **Hypotheses**: window shape `0 < a`, `0 < b`, `b ≤ a`; the two exactness identities; and
  (implicitly, by instance search) that `B^I` is already known Tate.
- **Uses from project**: `isTateRing_congr`, `presheafChartRingEquivBISub`,
  `presheafChartRingEquivBISub_symm_continuous`, `presheafChartRingEquivBISub_continuous`,
  `presheafValue`, `chartData`, `perfectoidValuation`.
- **Used by**: `chartVObj`.
- **Visibility**: public
- **Lines**: 55–69 (term body 9 lines)
- **Notes**: `noncomputable`; a `def` rather than `instance` so it can be introduced locally.

---

### `def chartVObj`

- **Type**:
  `chartVObj (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 …) (hexact2 …) : VObj`
- **What**: **The headline object of the file** — `Spa` of a Big-window chart of the
  Fargues–Fontaine `𝒴`, packaged as an object of Wedhorn's category `𝒱` (a locally ringed space
  with a sheaf of topological rings, local stalks and stalk valuations).
- **How**: Assembles, as local instances on the chart value, everything `spaVObj_of_isSheafy`
  (Wedhorn 8.14/8.20) demands: the plus structure `chartPlus`; `IsHuberRing` from
  `chartTate.toIsHuberRing`; right-uniformity completeness from
  `completeSpace_right_presheafValue`; `IsRingOfIntegralElements` for the plus subring by
  transporting `isRingOfIntegralElements_BIPlusIn` along `presheafChartRingEquivBISub.symm` via
  `IsRingOfIntegralElements.map`; and sheafiness from `isSheafy_presheafChart`.
- **Hypotheses**: window shape `0 < a`, `0 < b`, `b ≤ a`; the two exactness identities pinning
  `ρ₁, ρ₂` to the chart window (they are what makes the comparison isomorphism available).
- **Uses from project**: `chartPlus`, `chartTate`, `completeSpace_right_presheafValue`,
  `isRingOfIntegralElements_BIPlusIn`, `IsRingOfIntegralElements.map`,
  `presheafChartRingEquivBISub`, `presheafChartRingEquivBISub_symm_continuous`,
  `presheafChartRingEquivBISub_continuous`, `isSheafy_presheafChart`, `spaVObj_of_isSheafy`,
  `ValuationSpectrum.ringPlus`, `ValuationSpectrum.IsSheafy`, `presheafValue`, `chartData`, `VObj`.
- **Used by**: unused in file (and currently unused elsewhere in the project).
- **Visibility**: public
- **Lines**: 75–108 (term body ~28 lines of `letI`/`haveI` instance plumbing)
- **Notes**: `noncomputable`. Body >30 lines is instance assembly, not a proof. Relies on the
  file-level `linter.overlappingInstances` suppression (several plus/uniformity instances coexist).

---

### `theorem presheafChartRingEquivBISub_isOpenMap`

- **Type**:
  `… : IsOpenMap (presheafChartRingEquivBISub p F ϖ … a b ha hb hab hexact1 hexact2)`
- **What**: The forward ID2 comparison map `O(U_{a,b}) → B^I` is an open map.
- **How**: A bijection's image of `U` is the preimage of `U` under its inverse
  (`Equiv.image_eq_preimage_symm`), and that preimage is open because
  `presheafChartRingEquivBISub_symm_continuous` gives continuity of the inverse
  (`Continuous.isOpen_preimage`).
- **Hypotheses**: window shape and the two exactness identities (needed only to name the
  comparison map).
- **Uses from project**: `presheafChartRingEquivBISub`,
  `presheafChartRingEquivBISub_symm_continuous`, `perfectoidValuation`.
- **Used by**: `completedPlusSubring_le_chartPlus`.
- **Visibility**: public
- **Lines**: 115–133 (proof 10 lines)
- **Notes**: none.

---

### `theorem completedPlusSubring_le_chartPlus`

- **Type**:
  `… : (chartData p F ϖ 1 b a b).completedPlusSubring ≤ (BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).map (presheafChartRingEquivBISub … ).symm.toRingHom`
- **What**: **The easy half of the plus reconciliation** (Kedlaya Def 4.5, ⊆): the canonical
  Wedhorn plus subring of the chart value is contained in the transported `B^I`-unit ball.
- **How**: Canonical-plus elements are power-bounded via
  `RationalLocData.presheafValuePlus_isRingOfIntegralElements.subset_powerBounded` (using
  `isAffinoidRing_Ainf` to supply the base `IsRingOfIntegralElements`); power-boundedness is carried
  forward by the continuous *open* ring hom (`isPowerBounded_map_of_isOpenMap` with
  `presheafChartRingEquivBISub_isOpenMap`); and in `B^I` power-bounded is exactly `wI ≤ 1`
  (`isPowerBounded_iff_wI_le_one`, `mem_BIPlusIn_iff`), giving the ball membership whose preimage
  witness is `e.symm_apply_apply`.
- **Hypotheses**: window shape `0 < a`, `0 < b`, `b ≤ a`; the two exactness identities; `A_inf` is
  affinoid (supplied inside the proof).
- **Uses from project**: `isAffinoidRing_Ainf`, `Ainf`,
  `RationalLocData.presheafValuePlus_isRingOfIntegralElements`, `isPowerBounded_map_of_isOpenMap`,
  `presheafChartRingEquivBISub`, `presheafChartRingEquivBISub_continuous`,
  `presheafChartRingEquivBISub_isOpenMap`, `mem_BIPlusIn_iff`, `isPowerBounded_iff_wI_le_one`,
  `BIPlusIn`, `chartData`, `RationalLocData.completedPlusSubring`.
- **Used by**: `chartPlus_map_eq_completedPlusSubring`.
- **Visibility**: public
- **Lines**: 140–183 (proof 33 lines)
- **Notes**: proof >30 lines.

---

### `def ChartDensePlus`

- **Type**:
  `ChartDensePlus (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 …) (hexact2 …) : Prop`
- **What**: The **dense-level integrality claim**: for every `h : Bloc` with both window Gauss norms
  `wLoc_{ρ₁} h ≤ 1` and `wLoc_{ρ₂} h ≤ 1`, the inverse comparison sends `blocToBI h` into the
  canonical `completedPlusSubring` of the chart value. This is the substantive half of Kedlaya
  Def 4.5, isolated as a named predicate so it can be assumed and later discharged.
- **How**: Definition only — a `∀`-statement over `Bloc p F ϖ` with the two `wLoc ≤ 1` hypotheses and
  membership of `e.symm (blocToBI h)` in `(chartData …).completedPlusSubring` as conclusion.
- **Hypotheses**: window shape and the two exactness identities (they make the comparison map exist);
  the predicate itself quantifies over the two Gauss-norm bounds.
- **Uses from project**: `Bloc`, `wLoc`, `presheafChartRingEquivBISub`, `blocToBI`, `chartData`,
  `RationalLocData.completedPlusSubring`, `perfectoidValuation`.
- **Used by**: `chartPlus_le_completedPlusSubring_of_dense` (as hypothesis),
  `chartDensePlus_of_exact` (as conclusion).
- **Visibility**: public
- **Lines**: 191–201 (body 5 lines)
- **Notes**: `Prop`-valued `def`, deliberately not an `abbrev` (kept opaque so the two theorems can
  quote it by name).

---

### `theorem exists_ball_approx`

- **Type**:
  `exists_ball_approx (z : ↥(BISub …)) (hz : z ∈ BIPlusIn …) (n : ℕ) : ∃ h : Bloc p F ϖ, wI … (z - BIProd … h) ≤ (2 : NNReal)⁻¹ ^ n ∧ wLoc … hρ₁0 hρ₁1 h ≤ 1 ∧ wLoc … hρ₂0 hρ₂1 h ≤ 1`
- **What**: Every unit-ball element of `B^I` is approximated to accuracy `2^{-n}` by a `Bloc`
  element which is *itself* in the unit ball at both radii (a ball-preserving density statement).
- **How**: `z` lies in the closure of the diagonal `Bloc`-image by the very definition of `BISub`
  (`z.2`); `mem_closure_iff_nhds` against the neighbourhood `wI_ball_mem_nhds` of radius
  `min (2^{-n}) 1` produces a `Bloc` witness `hh`; `wI_neg` flips the difference; the ultrametric
  inequality `wI_add_le` then bounds `wI (BIProd hh) ≤ max (wI diff) (wI z) ≤ 1`; finally
  `BIProd_fst` / `BIProd_snd` together with `valued_BlocToHatK` turn the two components of that
  `max` into the two `wLoc ≤ 1` conclusions.
- **Hypotheses**: `z` is in the ball `BIPlusIn` (i.e. `wI z ≤ 1`); the radii satisfy
  `0 < ρᵢ < 1` (from the ambient variables).
- **Uses from project**: `BISub`, `BIPlusIn`, `mem_BIPlusIn_iff`, `BIProd`, `BIProd_fst`,
  `BIProd_snd`, `wI`, `wI_neg`, `wI_add_le`, `wI_ball_mem_nhds`, `wLoc`, `valued_BlocToHatK`,
  `hatK`, `Bloc`.
- **Used by**: `chartPlus_le_completedPlusSubring_of_dense`.
- **Visibility**: public
- **Lines**: 204–252 (proof 42 lines)
- **Notes**: proof >30 lines; the `min (2⁻¹^n) 1` trick is what makes one closure extraction serve
  both the accuracy bound and the ball bound.

---

### `theorem chartPlus_le_completedPlusSubring_of_dense`

- **Type**:
  `… (hdense : ChartDensePlus … a b ha hb hab hexact1 hexact2) : (BIPlusIn …).map (presheafChartRingEquivBISub …).symm.toRingHom ≤ (chartData p F ϖ 1 b a b).completedPlusSubring`
- **What**: **The hard half of the plus reconciliation, reduced to the dense level**: assuming the
  dense-level integrality `ChartDensePlus`, the transported unit ball is contained in the canonical
  plus subring.
- **How**: A limit argument. `completedPlusSubring` is open — via
  `RationalLocData.presheafValuePlus_isRingOfIntegralElements.isOpen` (with `isAffinoidRing_Ainf`)
  — hence closed as an additive subgroup (`AddSubgroup.isClosed_of_isOpen`). For a ball element `z`,
  `exists_ball_approx` `choose`s ball-bounded `Bloc` approximants; these converge to `z` by
  `tendsto_subtype_rng` plus `tendsto_BIProd_of_valued_le` with `ε n = 2⁻¹ ^ n`
  (`glueSeq_eps_tendsto`), the two componentwise bounds coming from `BIProd_fst` / `BIProd_snd` and
  `Valuation.map_sub_swap`. Pushing through the continuous `e.symm` and applying
  `IsClosed.mem_of_tendsto` with `hdense` on each approximant gives the membership.
- **Hypotheses**: window shape; the two exactness identities; and crucially the dense-level
  integrality `hdense : ChartDensePlus …` (discharged later at `b = 1` by `chartDensePlus_of_exact`).
- **Uses from project**: `ChartDensePlus`, `exists_ball_approx`, `blocToBI`, `BIProd`, `BIProd_fst`,
  `BIProd_snd`, `BISub`, `BIPlusIn`, `hatK`, `tendsto_BIProd_of_valued_le`, `glueSeq_eps_tendsto`,
  `isAffinoidRing_Ainf`, `Ainf`, `RationalLocData.presheafValuePlus_isRingOfIntegralElements`,
  `presheafChartRingEquivBISub`, `presheafChartRingEquivBISub_symm_continuous`, `chartData`,
  `RationalLocData.completedPlusSubring`, `presheafValue`.
- **Used by**: `chartPlus_map_eq_completedPlusSubring`.
- **Visibility**: public
- **Lines**: 257–333 (proof 64 lines)
- **Notes**: proof >30 lines; the two symmetric `intro n … Valuation.map_sub_swap` blocks are
  duplicated for the `.1` and `.2` components (a decomposition candidate).

---

### `theorem exists_eq_toOF_pow_mul`

- **Type**:
  `exists_eq_toOF_pow_mul (j : ℕ) (c : OF F) (hc : perfectoidValuation p F c ≤ perfectoidValuation p F ϖ ^ j) : ∃ c' : OF F, c = (PseudoUniformizer.toOF F ϖ) ^ j * c'`
- **What**: Divisibility from the valuation comparison in the ring of integers `O_F`: an integral
  element of value at most `|ϖ|^j` is exactly `ϖ^j` times another integral element.
- **How**: Uses `(perfectoidValuation_integers p F).dvd_of_le` — the `Valuation.Integers` API turning
  a valuation inequality into a divisibility in the valuation ring — after massaging the goal's
  `algebraMap ↥(powerBoundedSubring.toSubring F) F` coercions to plain `O_F → F` coercions with
  `push_cast` and `map_pow`.
- **Hypotheses**: `perfectoidValuation p F c ≤ |ϖ|^j`; `perfectoidValuation` is a valuation whose
  integers are `O_F` (`perfectoidValuation_integers`).
- **Uses from project**: `perfectoidValuation`, `perfectoidValuation_integers`, `OF`,
  `PseudoUniformizer.toOF`.
- **Used by**: `teich_div_p_pow_mem_chartSubring`, `p_div_teich_pow_a_mem_chartSubring`,
  `mk_monomial_mem_of_le`, `mk_monomial_pow_a_eq`.
- **Visibility**: public
- **Lines**: 340–361 (proof 18 lines)
- **Notes**: one of the two most-reused lemmas of the file.

---

### `theorem teich_div_p_pow_mem_chartSubring`

- **Type**:
  `teich_div_p_pow_mem_chartSubring (a b j : ℕ) (c : OF F) (hc : perfectoidValuation p F c ≤ perfectoidValuation p F ϖ ^ j) : algebraMap (Ainf p F) (Bloc p F ϖ) (teichmuller p c) * (↑(isUnit_p_image p F ϖ).unit⁻¹) ^ j ∈ Subring.closure (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ)) ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b})`
- **What**: **(m1) Negative-monomial membership**: the Teichmüller monomial `[c]/p^j` satisfying the
  left-endpoint bound `|c| ≤ |ϖ|^j` lies in the chart subring `S` generated by the `A_inf`-image
  together with the two chart fractions.
- **How**: Factor `c = ϖ^j c'` with `exists_eq_toOF_pow_mul`, then the multiplicativity of
  `WittVector.teichmuller` and of `algebraMap` (`map_mul`, `map_pow`) plus the definition
  `chartFracPi = alg([ϖ]) * p⁻¹` rewrite the monomial as `chartFracPi ^ j * alg([c'])`; both factors
  are generators, so `Subring.subset_closure`, `pow_mem`, `mul_mem` close the goal.
- **Hypotheses**: the left-endpoint valuation bound `|c| ≤ |ϖ|^j`; `p` is a unit in `Bloc`
  (`isUnit_p_image`).
- **Uses from project**: `exists_eq_toOF_pow_mul`, `chartFracPi`, `chartFracP`, `teichPi`,
  `isUnit_p_image`, `Ainf`, `Bloc`, `OF`, `perfectoidValuation`, `PseudoUniformizer.toOF`.
- **Used by**: `mk_monomial_mem_of_le`.
- **Visibility**: public
- **Lines**: 366–390 (proof 17 lines)
- **Notes**: none.

---

### `theorem p_div_teich_pow_a_mem_chartSubring`

- **Type**:
  `p_div_teich_pow_a_mem_chartSubring (a b d : ℕ) (hab : b ≤ a) (c' : OF F) (hc : perfectoidValuation p F c' ^ a ≤ perfectoidValuation p F ϖ ^ (d * (a - b))) : (alg (p)^d * AlocToBloc (teichPiInvAloc)^d * alg (teichmuller p c'))^a ∈ Subring.closure (range alg ∪ {chartFracPi, chartFracP a b})`
- **What**: **(m3) Positive-monomial `a`-th-power membership**, general `b`: for the fraction monomial
  `(p/[ϖ])^d·[c']` obeying the right-endpoint bound `|c'|^a ≤ |ϖ|^{d(a−b)}`, its `a`-th power lies in
  the chart subring — the monic witness `X^a − s₀` making the monomial integral over `S`.
- **How**: `exists_eq_toOF_pow_mul` gives `(c')^a = ϖ^{d(a−b)} c''`; a `calc` chain then rewrites the
  `a`-th power as `chartFracP a b ^ d * alg([c''])`, using `AlocToBloc_teichPiInv_mul` (the identity
  `([ϖ]^{-1})^m · alg([ϖ])^m = 1`), the unfolding `chartFracP a b = alg(p)^a · ([ϖ]^{-1})^b`, and the
  exponent bookkeeping `d·a = d·b + d·(a−b)` (`omega`); membership then follows from
  `Subring.subset_closure`, `pow_mem`, `mul_mem`.
- **Hypotheses**: `b ≤ a`; the right-endpoint bound `|c'|^a ≤ |ϖ|^{d(a−b)}`.
- **Uses from project**: `exists_eq_toOF_pow_mul`, `AlocToBloc`, `teichPiInvAloc`,
  `AlocToBloc_teichPiInv_mul`, `teichPi`, `chartFracP`, `chartFracPi`, `Ainf`, `Bloc`, `OF`,
  `perfectoidValuation`, `PseudoUniformizer.toOF`.
- **Used by**: unused in file (the `b = 1` route goes through `mk_monomial_pow_a_eq` instead;
  this is the general-`b` sibling kept for the future general window).
- **Visibility**: public
- **Lines**: 396–489 (proof 83 lines)
- **Notes**: proof >30 lines; substantial `calc` block of pure monoid/exponent algebra.

---

### `def sPow`

- **Type**: `sPow (k : ℕ) : Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)`
- **What**: The `k`-th power of the chart denominator `s = p·[ϖ]`, packaged as an element of the
  localization submonoid (so it can be used as the denominator of `IsLocalization.mk'`).
- **How**: The subtype element `⟨(p·[ϖ])^k, ⟨k, rfl⟩⟩` — the power together with its membership
  witness in `Submonoid.powers`.
- **Hypotheses**: none beyond the ambient `p`, `F`, `ϖ`.
- **Uses from project**: `Ainf`, `teichPi`.
- **Used by**: `mk_monomial_mem_of_large`, `mk_monomial_mem_of_le`, `mk_monomial_pow_a_eq`,
  `monomial_symm_blocToBI_mem_completedPlusSubring`, `gaussValue_sPow`,
  `gaussTerm_le_of_wLoc_mk'_le_one`, `mk'_sPow_split`, `wLoc_mk'_tail_le`, `chartDensePlus_of_exact`
  (9 consumers — the most reused declaration in the file).
- **Visibility**: public
- **Lines**: 495–496 (body 1 line)
- **Notes**: none.

---

### `theorem mk_monomial_mem_of_large`

- **Type**:
  `mk_monomial_mem_of_large (a k i : ℕ) (hik : k * a + k ≤ i) (c : OF F) : IsLocalization.mk' (Bloc p F ϖ) ((p : Ainf p F) ^ i * teichmuller p c) (sPow p F ϖ k) ∈ Subring.closure (range alg ∪ {chartFracPi, chartFracP a 1})`
- **What**: **(M3'') Large-exponent zone** (`b = 1`): when `i ≥ ka + k` the monomial fraction
  `p^i[c]/(p[ϖ])^k` needs no valuation hypothesis at all — it is `chartFracP^k` times an
  `A_inf`-image, hence directly in the chart subring.
- **How**: `IsLocalization.mk'_eq_iff_eq_mul` reduces to an identity in `Bloc`; a `calc` splits
  `p^i = p^{ka}·p^{i−(ka+k)}·p^k` (exponent split by `omega`), inserts the unit factor
  `1 = ([ϖ]^{-1})^k·alg([ϖ])^k` from `AlocToBloc_teichPiInv_mul`, and closes with
  `generalize` + `ring` after unfolding `chartFracP a 1 = alg(p)^a · [ϖ]^{-1}`.
- **Hypotheses**: `k * a + k ≤ i` (the right-hand zone boundary); `b = 1` is baked into the
  statement via `chartFracP p F ϖ a 1`.
- **Uses from project**: `sPow`, `chartFracP`, `chartFracPi`, `AlocToBloc`, `teichPiInvAloc`,
  `AlocToBloc_teichPiInv_mul`, `teichPi`, `Ainf`, `Bloc`, `OF`.
- **Used by**: `monomial_symm_blocToBI_mem_completedPlusSubring` (zone M3).
- **Visibility**: public
- **Lines**: 501–569 (proof 63 lines)
- **Notes**: proof >30 lines; uses `generalize` to hide the four atoms before `ring`.

---

### `theorem mk_monomial_mem_of_le`

- **Type**:
  `mk_monomial_mem_of_le (a k i : ℕ) (hik : i ≤ k) (c : OF F) (hc : perfectoidValuation p F c ≤ perfectoidValuation p F ϖ ^ (2 * k - i)) : IsLocalization.mk' (Bloc p F ϖ) ((p : Ainf p F) ^ i * teichmuller p c) (sPow p F ϖ k) ∈ Subring.closure (range alg ∪ {chartFracPi, chartFracP a 1})`
- **What**: **(M1'') Small-exponent zone** (`b = 1`): for `i ≤ k` with the left-endpoint bound
  `|c| ≤ |ϖ|^{2k−i}`, the monomial fraction `p^i[c]/(p[ϖ])^k` is an `m1`-form element `[c']·p^{-(k−i)}`
  and hence a chart-subring element.
- **How**: From `hc` and `pow_le_pow_of_le_one` (with `perfectoidValuation_toOF_lt_one`) get
  `|c| ≤ |ϖ|^k`, so `exists_eq_toOF_pow_mul` factors `c = ϖ^k c'`; cancelling `|ϖ|^k`
  (`le_of_mul_le_mul_left`, positivity from `vpi_pos`) yields `|c'| ≤ |ϖ|^{k−i}`. A `calc` using
  `IsLocalization.mk'_eq_iff_eq_mul` and the unit cancellation `(p^{-1})^{k−i}·p^{k−i} = 1`
  (from `isUnit_p_image`) rewrites the fraction as `alg([c'])·(p^{-1})^{k−i}`, and
  `teich_div_p_pow_mem_chartSubring` finishes.
- **Hypotheses**: `i ≤ k`; the left-endpoint Gauss bound `|c| ≤ |ϖ|^{2k−i}`; `|ϖ| > 0` and `< 1`.
- **Uses from project**: `vpi_pos`, `perfectoidValuation_toOF_lt_one`, `exists_eq_toOF_pow_mul`,
  `isUnit_p_image`, `teichPi`, `sPow`, `chartFracP`, `chartFracPi`,
  `teich_div_p_pow_mem_chartSubring`, `Ainf`, `Bloc`, `OF`, `perfectoidValuation`.
- **Used by**: `monomial_symm_blocToBI_mem_completedPlusSubring` (zone M1).
- **Visibility**: public
- **Lines**: 574–674 (proof 92 lines)
- **Notes**: proof >30 lines; longest of the three zone lemmas.

---

### `theorem mk_monomial_pow_a_eq`

- **Type**:
  `mk_monomial_pow_a_eq (a k d : ℕ) (hd : d ≤ k * a) (c : OF F) (hc : perfectoidValuation p F c ^ a ≤ perfectoidValuation p F ϖ ^ (k * a - d)) : ∃ c'' : OF F, (IsLocalization.mk' (Bloc p F ϖ) ((p : Ainf p F) ^ (k + d) * teichmuller p c) (sPow p F ϖ k)) ^ a = chartFracP p F ϖ a 1 ^ d * algebraMap (Ainf p F) (Bloc p F ϖ) (teichmuller p c'')`
- **What**: **(M2'') Middle-zone `a`-th-power identity** (`b = 1`): for `0 < d ≤ ka` the `a`-th power
  of the monomial fraction `p^{k+d}[c]/(p[ϖ])^k`, under the right-endpoint bound
  `|c|^a ≤ |ϖ|^{ka−d}`, equals `chartFracP^d` times a Teichmüller image — the monic witness making
  the monomial integral over the chart subring.
- **How**: Two steps. First the `mk'`-power collapse `(mk' n (s^k))^a = mk' (n^a) (s^{ka})`, proved by
  `IsLocalization.mk'_eq_iff_eq_mul` together with `IsLocalization.mk'_spec` and `← pow_mul`. Then
  `exists_eq_toOF_pow_mul` gives `c^a = ϖ^{ka−d}c''`, and a `calc` chain inserts
  `1 = ([ϖ]^{-1})^d·alg([ϖ])^d` (`AlocToBloc_teichPiInv_mul`), rewrites `(k+d)a = ad + ka` and
  `alg([ϖ])^{ka} = alg([ϖ])^{ka−d}·alg([ϖ])^d`, and finishes by `generalize` + `ring`.
- **Hypotheses**: `d ≤ k * a`; the right-endpoint Gauss bound `|c|^a ≤ |ϖ|^{ka−d}`; `b = 1`.
- **Uses from project**: `exists_eq_toOF_pow_mul`, `AlocToBloc`, `teichPiInvAloc`,
  `AlocToBloc_teichPiInv_mul`, `chartFracP`, `teichPi`, `sPow`, `Ainf`, `Bloc`, `OF`,
  `perfectoidValuation`, `PseudoUniformizer.toOF`.
- **Used by**: `monomial_symm_blocToBI_mem_completedPlusSubring` (zone M2).
- **Visibility**: public
- **Lines**: 681–781 (proof 90 lines)
- **Notes**: proof >30 lines; the `refine ⟨c'', ?_⟩` + `rw [show … from ?_]` structure defers the
  `mk'`-power collapse to the second bullet.

---

### `theorem presheafChartRingEquivBISub_symm_blocToBI`

- **Type**:
  `… (h : Bloc p F ϖ) : (presheafChartRingEquivBISub … a b ha hb hab hexact1 hexact2).symm (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 h) = (chartData p F ϖ 1 b a b).coeRingHom ((blocEquivAwayChartS p F ϖ b hb).symm h)`
- **What**: **The transport law** — the backbone of the whole `ChartDensePlus` argument: the inverse
  comparison map sends the diagonal `B^I`-image of a `Bloc` element to the completion-coercion of
  that element's chart-localization avatar.
- **How**: Apply injectivity of `e` and `RingEquiv.apply_symm_apply`, reducing to a forward
  computation. `presheafChartToBI_eq_compare` identifies the forward map with the abstract-completion
  comparison, and `AbstractCompletion.compare_coe` (instantiated at `chartUniformity`,
  `UniformSpace.Completion.cPkg` and `chartBIPkg`) says a comparison map sends `coe x` to the other
  package's `coe x` — here `chartToBI`. The remaining goal is `Subtype.ext`-reduced to
  `BIProd h = BIProd (blocEquivAwayChartS (blocEquivAwayChartS.symm h))`, closed by
  `RingEquiv.apply_symm_apply`.
- **Hypotheses**: window shape `0 < a`, `0 < b`, `b ≤ a`; the two exactness identities (they feed
  `vpi_le_rho2_of_exact` and `rho1_pow_le_of_exact` for the `presheafChartToBI` bound arguments).
- **Uses from project**: `presheafChartRingEquivBISub`, `blocToBI`, `chartData`,
  `RationalLocData.coeRingHom`, `blocEquivAwayChartS`, `chartCompletionUniformEquiv`, `chartToBI`,
  `chartUniformity`, `chartBIPkg`, `presheafChartToBI`, `presheafChartToBI_eq_compare`,
  `vpi_le_rho2_of_exact`, `rho1_pow_le_of_exact`, `BIProd`, `Bloc`, `perfectoidValuation`.
- **Used by**: `symm_blocToBI_mem_completedPlusSubring_of_mem`,
  `symm_blocToBI_mem_completedPlusSubring_of_pow_mem`.
- **Visibility**: public
- **Lines**: 788–845 (proof 46 lines)
- **Notes**: proof >30 lines; uses an explicit `@AbstractCompletion.compare_coe` application with the
  uniformity instance supplied positionally (the instance is not inferable).

---

### `theorem chartSubring_le_locPlusSubring_map`

- **Type**:
  `chartSubring_le_locPlusSubring_map (a b : ℕ) (hb : 0 < b) : Subring.closure (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ)) ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b}) ≤ ((chartData p F ϖ 1 b a b).locPlusSubring).map (blocEquivAwayChartS p F ϖ b hb).toRingHom`
- **What**: The chart subring `S ⊆ Bloc` (generated by the `A_inf`-image and the two chart fractions)
  is contained in the image of Wedhorn's `A⁺[T/s]` under the chart identification
  `Localization.Away (chartS) ≃+* Bloc`.
- **How**: `Subring.closure_le` reduces to checking generators. `A_inf`-images: use
  `RationalLocData.algebraMap_Aplus_mem_locPlusSubring` (with `A⁺ = ⊤` for the non-Tate pair
  `(A_inf, A_inf)`, hence `Subring.mem_top`) and `blocEquivAwayChartS_algebraMap`. The two fractions:
  they are the images of `divByS ([ϖ]^{b+1}) s` and `divByS (p^{a+1}) s`, which lie in
  `locPlusSubring` by `RationalLocData.divByS_mem_locPlusSubring` since `chartT a b = {p^{a+1},
  [ϖ]^{b+1}}`; the identifications are `blocEquiv_divByS_teichPi` and `blocEquiv_divByS_p`.
- **Hypotheses**: `0 < b` (needed for the chart-localization identification `blocEquivAwayChartS`).
- **Uses from project**: `Ainf`, `Bloc`, `chartFracPi`, `chartFracP`, `chartData`, `chartS`,
  `chartT`, `divByS`, `RationalLocData.locPlusSubring`,
  `RationalLocData.algebraMap_Aplus_mem_locPlusSubring`,
  `RationalLocData.divByS_mem_locPlusSubring`, `blocEquivAwayChartS`,
  `blocEquivAwayChartS_algebraMap`, `blocEquiv_divByS_teichPi`, `blocEquiv_divByS_p`, `teichPi`.
- **Used by**: `coeRingHom_mem_completedPlusSubringBase_of_mem`.
- **Visibility**: public
- **Lines**: 849–872 (proof 18 lines)
- **Notes**: none.

---

### `theorem coeRingHom_mem_completedPlusSubringBase_of_mem`

- **Type**:
  `coeRingHom_mem_completedPlusSubringBase_of_mem (a b : ℕ) (hb : 0 < b) {h : Bloc p F ϖ} (hS : h ∈ Subring.closure (range alg ∪ {chartFracPi, chartFracP a b})) : (chartData p F ϖ 1 b a b).coeRingHom ((blocEquivAwayChartS p F ϖ b hb).symm h) ∈ (chartData p F ϖ 1 b a b).completedPlusSubringBase`
- **What**: Chart-subring elements, pulled back to the localization and pushed into the completion,
  land in `completedPlusSubringBase` (the topological closure of the image of `(A⁺[T/s])^int`).
- **How**: `chartSubring_le_locPlusSubring_map` supplies a preimage `w ∈ locPlusSubring`;
  every element of `locPlusSubring` is trivially integral over itself
  (`isIntegral_algebraMap` on the subtype), so `w` lies in the integral closure; finally
  `Subring.le_topologicalClosure` puts its `coeRingHom`-image in the topological closure that
  defines `completedPlusSubringBase`.
- **Hypotheses**: `0 < b`; membership `hS` of `h` in the chart subring.
- **Uses from project**: `chartSubring_le_locPlusSubring_map`, `blocEquivAwayChartS`, `chartData`,
  `RationalLocData.locPlusSubring`, `RationalLocData.completedPlusSubringBase`,
  `RationalLocData.coeRingHom`, `chartFracPi`, `chartFracP`, `Ainf`, `Bloc`.
- **Used by**: `symm_blocToBI_mem_completedPlusSubring_of_mem`,
  `symm_blocToBI_mem_completedPlusSubring_of_pow_mem`.
- **Visibility**: public
- **Lines**: 875–896 (proof 14 lines)
- **Notes**: none.

---

### `theorem symm_blocToBI_mem_completedPlusSubring_of_mem`

- **Type**:
  `… {h : Bloc p F ϖ} (hS : h ∈ Subring.closure (range alg ∪ {chartFracPi, chartFracP a b})) : (presheafChartRingEquivBISub …).symm (blocToBI … h) ∈ (chartData p F ϖ 1 b a b).completedPlusSubring`
- **What**: Chart-subring (`S`) members transport into the canonical plus subring of the chart value.
- **How**: Rewrite the left side with the transport law
  `presheafChartRingEquivBISub_symm_blocToBI`, then chain
  `coeRingHom_mem_completedPlusSubringBase_of_mem` with
  `RationalLocData.completedPlusSubringBase_le_completedPlusSubring`.
- **Hypotheses**: window shape; the two exactness identities; membership `hS` in the chart subring.
- **Uses from project**: `presheafChartRingEquivBISub_symm_blocToBI`,
  `coeRingHom_mem_completedPlusSubringBase_of_mem`,
  `RationalLocData.completedPlusSubringBase_le_completedPlusSubring`,
  `presheafChartRingEquivBISub`, `blocToBI`, `chartData`, `chartFracPi`, `chartFracP`, `Ainf`,
  `Bloc`, `perfectoidValuation`.
- **Used by**: `monomial_symm_blocToBI_mem_completedPlusSubring` (zones M1 and M3).
- **Visibility**: public
- **Lines**: 899–916 (proof 4 lines)
- **Notes**: none.

---

### `theorem symm_blocToBI_mem_completedPlusSubring_of_pow_mem`

- **Type**:
  `… {n : ℕ} (hn : 0 < n) {h : Bloc p F ϖ} (hS : h ^ n ∈ Subring.closure (range alg ∪ {chartFracPi, chartFracP a b})) : (presheafChartRingEquivBISub …).symm (blocToBI … h) ∈ (chartData p F ϖ 1 b a b).completedPlusSubring`
- **What**: The integrality version: it suffices that some positive power `h^n` lies in the chart
  subring — the element is then integral (monic `X^n − s₀`) over the plus base, hence in the
  canonical plus subring.
- **How**: Rewrite with `presheafChartRingEquivBISub_symm_blocToBI`; move the power across the two
  ring homs (`map_pow` for `blocEquivAwayChartS.symm` and for `coeRingHom`) so that
  `coeRingHom_mem_completedPlusSubringBase_of_mem` applies to the `n`-th power; then
  `isIntegral_algebraMap` makes that power integral over `completedPlusSubringBase` and
  `IsIntegral.of_pow hn` descends integrality to the element itself, which is exactly membership in
  `completedPlusSubring` (`Subalgebra.mem_toSubring`).
- **Hypotheses**: `0 < n`; `h^n` in the chart subring; window shape and exactness identities.
- **Uses from project**: `presheafChartRingEquivBISub_symm_blocToBI`,
  `coeRingHom_mem_completedPlusSubringBase_of_mem`, `RationalLocData.completedPlusSubringBase`,
  `RationalLocData.completedPlusSubring`, `RationalLocData.coeRingHom`, `blocEquivAwayChartS`,
  `presheafChartRingEquivBISub`, `blocToBI`, `chartData`, `chartFracPi`, `chartFracP`, `Ainf`,
  `Bloc`.
- **Used by**: `monomial_symm_blocToBI_mem_completedPlusSubring` (zone M2).
- **Visibility**: public
- **Lines**: 920–959 (proof 26 lines)
- **Notes**: none.

---

### `theorem monomial_symm_blocToBI_mem_completedPlusSubring`

- **Type**:
  `monomial_symm_blocToBI_mem_completedPlusSubring (a : ℕ) (ha : 0 < a) (hexact1 …) (hexact2 : ρ₂ ^ a = perfectoidValuation p F ϖ ^ 1) (k i : ℕ) (c : OF F) (hc1 : ρ₁ ^ i * |c| ≤ (ρ₁ * |ϖ|) ^ k) (hc2 : ρ₂ ^ i * |c| ≤ (ρ₂ * |ϖ|) ^ k) : (presheafChartRingEquivBISub … a 1 …).symm (blocToBI … (IsLocalization.mk' (Bloc p F ϖ) (p ^ i * teichmuller p c) (sPow p F ϖ k))) ∈ (chartData p F ϖ 1 1 a 1).completedPlusSubring`
- **What**: **Zone dispatch** (`b = 1`): a single monomial fraction `p^i[c]/(p[ϖ])^k` whose
  coefficient obeys both window Gauss-term bounds transports into the canonical plus subring.
- **How**: `by_cases` on the exponent `i` in three zones. (M1) `i ≤ k`: rewrite `hc1` with
  `hexact1` and the exponent identity `2k = i + (2k − i)`, cancel `|ϖ|^i`
  (`le_of_mul_le_mul_left`, `vpi_pos`) to get the left-endpoint bound, then
  `mk_monomial_mem_of_le` + `symm_blocToBI_mem_completedPlusSubring_of_mem`. (M2) `k < i ≤ ka+k`:
  raise `hc2` to the `a`-th power (`pow_le_pow_left'`) and use `hexact2` (`ρ₂^a = |ϖ|`) to convert it
  into `|c|^a ≤ |ϖ|^{ka−(i−k)}`, then `mk_monomial_pow_a_eq` supplies the monic witness and
  `symm_blocToBI_mem_completedPlusSubring_of_pow_mem` concludes. (M3) `i > ka+k`:
  `mk_monomial_mem_of_large` + `symm_blocToBI_mem_completedPlusSubring_of_mem`.
- **Hypotheses**: `0 < a`; the two exactness identities at `b = 1` (`|ϖ| = ρ₁` and `ρ₂^a = |ϖ|`);
  the two per-coefficient Gauss-term bounds `hc1`, `hc2` at the two radii.
- **Uses from project**: `vpi_pos`, `mk_monomial_mem_of_le`, `mk_monomial_pow_a_eq`,
  `mk_monomial_mem_of_large`, `symm_blocToBI_mem_completedPlusSubring_of_mem`,
  `symm_blocToBI_mem_completedPlusSubring_of_pow_mem`, `sPow`, `chartFracP`, `chartFracPi`,
  `presheafChartRingEquivBISub`, `blocToBI`, `chartData`, `Ainf`, `Bloc`, `OF`,
  `perfectoidValuation`, `PseudoUniformizer.toOF`.
- **Used by**: `chartDensePlus_of_exact`.
- **Visibility**: public
- **Lines**: 965–1044 (proof 61 lines)
- **Notes**: proof >30 lines; this is where the `b = 1` restriction enters (via `chartFracP … a 1`
  and `hexact2` with exponent `1`).

---

### `theorem gaussValue_sPow`

- **Type**:
  `gaussValue_sPow {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (k : ℕ) : gaussValue p F ρ ((sPow p F ϖ k : Ainf p F)) = (ρ * perfectoidValuation p F ϖ) ^ k`
- **What**: Computes the Gauss value of the chart denominator: `|(p[ϖ])^k|_ρ = (ρ·|ϖ|)^k`.
- **How**: Unfold `sPow k` to `(p·[ϖ])^k`, convert `gaussValue` into the valuation `gaussVal` via
  `gaussVal_apply`, use multiplicativity `Valuation.map_pow`, and finish with the base case
  `gaussValue_p_teichPi` (`|p[ϖ]|_ρ = ρ·|ϖ|`).
- **Hypotheses**: `0 < ρ < 1` (needed for `gaussVal` to be a valuation).
- **Uses from project**: `sPow`, `gaussValue`, `gaussVal`, `gaussVal_apply`, `gaussValue_p_teichPi`,
  `teichPi`, `Ainf`, `perfectoidValuation`, `PseudoUniformizer.toOF`.
- **Used by**: `gaussTerm_le_of_wLoc_mk'_le_one`, `wLoc_mk'_tail_le`.
- **Visibility**: public
- **Lines**: 1050–1060 (proof 7 lines)
- **Notes**: none.

---

### `theorem gaussTerm_le_of_wLoc_mk'_le_one`

- **Type**:
  `gaussTerm_le_of_wLoc_mk'_le_one {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x : Ainf p F) (k : ℕ) (hw : wLoc p F ϖ hρ0 hρ1 (IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k)) ≤ 1) (i : ℕ) : ρ ^ i * perfectoidValuation p F (teichCoeff p F x i) ≤ (ρ * perfectoidValuation p F ϖ) ^ k`
- **What**: **Per-coefficient bound from the localized unit-ball condition**: if the fraction
  `x/(p[ϖ])^k` has `wLoc ≤ 1`, then *every* Teichmüller Gauss term `ρ^i·|c_i|` of the numerator is
  bounded by the denominator's Gauss value.
- **How**: `wLoc_mk'` expresses `wLoc (mk' x s^k) = gaussValue ρ x · (gaussValue ρ s^k)⁻¹`; with
  `gaussValue_sPow` and the nonvanishing of `(ρ|ϖ|)^k` (from `vpi_pos`), a short `calc` multiplying
  through by that value converts `≤ 1` into `gaussValue ρ x ≤ (ρ|ϖ|)^k`. Since `gaussValue` is a
  supremum of the Gauss terms, `le_ciSup` with `bddAbove_range_gaussTerm` bounds the individual
  term by it.
- **Hypotheses**: `0 < ρ < 1`; `wLoc(mk' x (sPow k)) ≤ 1`; boundedness of the Gauss-term family
  (`bddAbove_range_gaussTerm`, needs `ρ ≤ 1`).
- **Uses from project**: `wLoc`, `wLoc_mk'`, `gaussValue`, `gaussValue_sPow`, `sPow`,
  `bddAbove_range_gaussTerm`, `teichCoeff`, `vpi_pos`, `Ainf`, `Bloc`, `perfectoidValuation`,
  `PseudoUniformizer.toOF`.
- **Used by**: `chartDensePlus_of_exact` (applied at both radii).
- **Visibility**: public
- **Lines**: 1065–1091 (proof 20 lines)
- **Notes**: none.

---

### `theorem mk'_sPow_split`

- **Type**:
  `mk'_sPow_split (x : Ainf p F) (k N : ℕ) (w : Ainf p F) (hw : x - ∑ i ∈ Finset.Iic N, teichmuller p (teichCoeff p F x i) * p ^ i = p ^ (N + 1) * w) : IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k) = (∑ i ∈ Finset.Iic N, IsLocalization.mk' (Bloc p F ϖ) (p ^ i * teichmuller p (teichCoeff p F x i)) (sPow p F ϖ k)) + IsLocalization.mk' (Bloc p F ϖ) (p ^ (N + 1) * w) (sPow p F ϖ k)`
- **What**: **The head/tail split of a localized element**: given a Teichmüller truncation witness
  for `x` at level `N`, the fraction `x/(p[ϖ])^k` splits as the sum of the `N`-truncated Teichmüller
  head fractions plus the `p^{N+1}`-tail fraction.
- **How**: The witness `hw` is rearranged (with `Finset.sum_congr` and `mul_comm` to normalise the
  factor order, then `ring`) into `x = ∑ p^i[c_i] + p^{N+1}w`; the fraction is then distributed using
  `IsLocalization.mk'_eq_mul_mk'_one` together with `map_add`, `map_sum`, `add_mul` and
  `Finset.sum_mul`, and re-folded by `simp only [← IsLocalization.mk'_eq_mul_mk'_one]`.
- **Hypotheses**: the truncation witness `hw` (supplied downstream by
  `WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff`).
- **Uses from project**: `sPow`, `teichCoeff`, `Ainf`, `Bloc`.
- **Used by**: `chartDensePlus_of_exact`.
- **Visibility**: public
- **Lines**: 1095–1124 (proof 19 lines)
- **Notes**: none.

---

### `theorem wLoc_mk'_tail_le`

- **Type**:
  `wLoc_mk'_tail_le {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (k N : ℕ) (w : Ainf p F) : wLoc p F ϖ hρ0 hρ1 (IsLocalization.mk' (Bloc p F ϖ) (p ^ (N + 1) * w) (sPow p F ϖ k)) ≤ ρ ^ (N + 1) * ((ρ * perfectoidValuation p F ϖ) ^ k)⁻¹`
- **What**: **The tail bound**: the localized `p^{N+1}`-tail has `wLoc` at most `ρ^{N+1}` divided by
  the denominator's Gauss value — a geometric decay in `N`.
- **How**: `wLoc_mk'` plus `gaussValue_sPow` reduce to bounding `gaussValue ρ (p^{N+1} w)`;
  multiplicativity of `gaussVal` (`gaussVal_apply`, `Valuation.map_mul`) together with
  `gaussVal_p_pow` gives `= ρ^{N+1}·gaussValue ρ w`, and `gaussValue_le_one` bounds the remaining
  factor by `1`.
- **Hypotheses**: `0 < ρ < 1` (so `gaussVal` is a valuation and `gaussValue_le_one` applies).
- **Uses from project**: `wLoc`, `wLoc_mk'`, `gaussValue_sPow`, `gaussValue`, `gaussVal`,
  `gaussVal_apply`, `gaussVal_p_pow`, `gaussValue_le_one`, `sPow`, `Ainf`, `Bloc`,
  `perfectoidValuation`, `PseudoUniformizer.toOF`.
- **Used by**: `chartDensePlus_of_exact` (at both radii).
- **Visibility**: public
- **Lines**: 1128–1148 (proof 14 lines)
- **Notes**: none.

---

### `theorem valued_BlocToHatK_sub_of_add`

- **Type**:
  `valued_BlocToHatK_sub_of_add {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (g t f : Bloc p F ϖ) (hf : f = g + t) : Valued.v (BlocToHatK p F ϖ hρ0 hρ1 g - BlocToHatK p F ϖ hρ0 hρ1 f) = wLoc p F ϖ hρ0 hρ1 t`
- **What**: Across an additive split `f = g + t`, the `hatK_ρ`-distance between the images of `g` and
  `f` is exactly the `wLoc`-size of the increment `t`.
- **How**: Substitute `hf`, use additivity of `BlocToHatK` (`map_add`), simplify
  `X − (X + Y) = −Y` by `ring`, kill the sign with `Valuation.map_neg`, and apply the project's
  compatibility `valued_BlocToHatK` (`v ∘ BlocToHatK = wLoc`).
- **Hypotheses**: `0 < ρ < 1`; the split `f = g + t`.
- **Uses from project**: `BlocToHatK`, `valued_BlocToHatK`, `wLoc`, `Bloc`.
- **Used by**: `chartDensePlus_of_exact` (at both radii).
- **Visibility**: public
- **Lines**: 1151–1160 (proof 6 lines)
- **Notes**: none.

---

### `theorem tendsto_max_const_mul_pow`

- **Type**:
  `tendsto_max_const_mul_pow (c₁ c₂ : NNReal) : Filter.Tendsto (fun N : ℕ => max (c₁ * ρ₁ ^ N) (c₂ * ρ₂ ^ N)) Filter.atTop (nhds 0)`
- **What**: The two-radius geometric error sequence `max (c₁ρ₁^N) (c₂ρ₂^N)` tends to `0` — the
  accuracy sequence for the head/tail approximation at both endpoints of the annulus.
- **How**: Each factor tends to `0` by `tendsto_pow_atTop_nhds_zero_of_lt_one` (using `hρ₁1`, `hρ₂1`)
  composed with `Filter.Tendsto.const_mul`; the max of two null sequences is null by
  `Filter.Tendsto.max` (`simpa` handles the `max 0 0 = 0` normalisation).
- **Hypotheses**: `ρ₁ < 1` and `ρ₂ < 1` (explicitly `include`d — the only declaration in the file
  needing the `include` directive).
- **Uses from project**: [] (only mathlib lemmas plus the ambient radius hypotheses).
- **Used by**: `chartDensePlus_of_exact`.
- **Visibility**: public
- **Lines**: 1162–1176 (`include hρ₁1 hρ₂1 in` at 1162; proof 10 lines)
- **Notes**: has an `include … in` modifier.

---

### `theorem chartDensePlus_of_exact`

- **Type**:
  `chartDensePlus_of_exact (a : ℕ) (ha : 0 < a) (hexact1 : perfectoidValuation p F ϖ = ρ₁) (hexact2 : ρ₂ ^ a = perfectoidValuation p F ϖ ^ 1) : ChartDensePlus p F ϖ … a 1 ha one_pos ha hexact1 hexact2`
- **What**: **The dense-level integrality theorem** (Kedlaya Def 4.5, `b = 1`) — the mathematical
  core of the file: every `Bloc` element bounded by `1` in both window Gauss norms transports into
  the canonical `completedPlusSubring` of the chart value.
- **How**: Reduce a general `h : Bloc` to `mk' x (sPow k)` via `IsLocalization.mk'_surjective` and
  `Submonoid.mem_powers_iff`. Extract per-coefficient bounds at both radii with
  `gaussTerm_le_of_wLoc_mk'_le_one`, and Teichmüller truncation witnesses with mathlib's
  `WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff`; `mk'_sPow_split` turns these into
  head/tail decompositions for every `N`. Each head is a finite sum of monomials, so `sum_mem` and
  `monomial_symm_blocToBI_mem_completedPlusSubring` place its transport in `completedPlusSubring`.
  The heads converge to `h` in `B^I` by `tendsto_BIProd_of_valued_le` with the accuracy sequence
  `max (ρ₁·(ρ₁|ϖ|)^{-k}·ρ₁^N) (ρ₂·(ρ₂|ϖ|)^{-k}·ρ₂^N)`, whose termwise bounds come from
  `valued_BlocToHatK_sub_of_add` + `wLoc_mk'_tail_le` and whose nullity is
  `tendsto_max_const_mul_pow`; `BIProd_fst`/`BIProd_snd` identify the limit pair. Finally the target
  is closed (`RationalLocData.presheafValuePlus_isRingOfIntegralElements.isOpen` with
  `isAffinoidRing_Ainf`, then `AddSubgroup.isClosed_of_isOpen`), so continuity of `e.symm` plus
  `IsClosed.mem_of_tendsto` transfers membership to the limit.
- **Hypotheses**: `0 < a`; the exact-window identities `|ϖ| = ρ₁` and `ρ₂^a = |ϖ|` (i.e. `b = 1`);
  `A_inf` affinoid (supplied in-proof).
- **Uses from project**: `ChartDensePlus`, `sPow`, `gaussTerm_le_of_wLoc_mk'_le_one`,
  `mk'_sPow_split`, `monomial_symm_blocToBI_mem_completedPlusSubring`, `wLoc_mk'_tail_le`,
  `valued_BlocToHatK_sub_of_add`, `tendsto_max_const_mul_pow`, `tendsto_BIProd_of_valued_le`,
  `BIProd`, `BIProd_fst`, `BIProd_snd`, `BlocToHatK`, `blocToBI`, `hatK`, `teichCoeff`, `teichPi`,
  `isAffinoidRing_Ainf`, `Ainf`, `RationalLocData.presheafValuePlus_isRingOfIntegralElements`,
  `presheafChartRingEquivBISub`, `presheafChartRingEquivBISub_symm_continuous`, `chartData`,
  `presheafValue`, `RationalLocData.completedPlusSubring`, `Bloc`, `perfectoidValuation`.
- **Used by**: `chartPlus_map_eq_completedPlusSubring`.
- **Visibility**: public
- **Lines**: 1182–1292 (proof 103 lines)
- **Notes**: proof >30 lines — the longest in the file; no `sorry`, no heartbeat bump.

---

### `theorem chartPlus_map_eq_completedPlusSubring`

- **Type**:
  `chartPlus_map_eq_completedPlusSubring (a : ℕ) (ha : 0 < a) (hexact1 …) (hexact2 : ρ₂ ^ a = perfectoidValuation p F ϖ ^ 1) : (BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).map (presheafChartRingEquivBISub … a 1 ha one_pos ha hexact1 hexact2).symm.toRingHom = (chartData p F ϖ 1 1 a 1).completedPlusSubring`
- **What**: **The plus reconciliation** (Kedlaya Definition 4.5, `b = 1`): the transported
  `B^I`-unit ball *equals* the canonical completed plus subring of the chart value.
- **How**: `le_antisymm` of the two halves — `chartPlus_le_completedPlusSubring_of_dense` fed with
  `chartDensePlus_of_exact` (⊆), and `completedPlusSubring_le_chartPlus` (⊇).
- **Hypotheses**: `0 < a`; the exact-window identities `|ϖ| = ρ₁`, `ρ₂^a = |ϖ|` (the `b = 1` window).
- **Uses from project**: `chartPlus_le_completedPlusSubring_of_dense`, `chartDensePlus_of_exact`,
  `completedPlusSubring_le_chartPlus`, `BIPlusIn`, `presheafChartRingEquivBISub`, `chartData`,
  `RationalLocData.completedPlusSubring`, `perfectoidValuation`.
- **Used by**: `chartPlus_eq_canonical`.
- **Visibility**: public
- **Lines**: 1301–1320 (term proof 9 lines)
- **Notes**: none.

---

### `theorem chartPlus_eq_canonical`

- **Type**:
  `chartPlus_eq_canonical (a : ℕ) (ha : 0 < a) (hexact1 …) (hexact2 : ρ₂ ^ a = perfectoidValuation p F ϖ ^ 1) : (chartPlus p F ϖ … a 1 ha one_pos ha hexact1 hexact2).toSubring = (chartData p F ϖ 1 1 a 1).completedPlusSubring`
- **What**: The `PlusSubring`-level restatement of the reconciliation: the plus structure carried by
  `chartVObj` is definitionally the canonical Wedhorn plus subring, so the chart `VObj` is the
  honest `Spa(O(U), O(U)⁺)`.
- **How**: The `toSubring` field of `chartPlus` unfolds to the transported ball, so the statement is
  literally `chartPlus_map_eq_completedPlusSubring` (term-mode, definitional unfolding only).
- **Hypotheses**: `0 < a`; the exact-window identities at `b = 1`.
- **Uses from project**: `chartPlus`, `chartPlus_map_eq_completedPlusSubring`, `chartData`,
  `RationalLocData.completedPlusSubring`, `perfectoidValuation`.
- **Used by**: unused in file; consumed downstream by
  `projects/AdicSpaces/Adic spaces/FarguesFontaine/YStalks.lean:512`.
- **Visibility**: public
- **Lines**: 1324–1334 (term proof 2 lines)
- **Notes**: none.

---

### File Summary

- **Total declarations**: 30 (5 defs, 25 lemmas/theorems, 0 instances)
- **Key API (used by 3+ others)**:
  - `sPow` — 9 in-file consumers (`mk_monomial_mem_of_large`, `mk_monomial_mem_of_le`,
    `mk_monomial_pow_a_eq`, `monomial_symm_blocToBI_mem_completedPlusSubring`, `gaussValue_sPow`,
    `gaussTerm_le_of_wLoc_mk'_le_one`, `mk'_sPow_split`, `wLoc_mk'_tail_le`,
    `chartDensePlus_of_exact`)
  - `exists_eq_toOF_pow_mul` — 4 in-file consumers (`teich_div_p_pow_mem_chartSubring`,
    `p_div_teich_pow_a_mem_chartSubring`, `mk_monomial_mem_of_le`, `mk_monomial_pow_a_eq`)
  - (next tier, 2 consumers each: `ChartDensePlus`, `presheafChartRingEquivBISub_symm_blocToBI`,
    `coeRingHom_mem_completedPlusSubringBase_of_mem`, `symm_blocToBI_mem_completedPlusSubring_of_mem`,
    `gaussValue_sPow`, `valued_BlocToHatK_sub_of_add`)
- **Unused declarations** (no in-file consumer):
  - `chartVObj` — the file's headline object; currently not consumed anywhere in the project
  - `p_div_teich_pow_a_mem_chartSubring` — the general-`b` sibling of `mk_monomial_pow_a_eq`,
    kept for the general window but not on the `b = 1` path
  - `chartPlus_eq_canonical` — used downstream in `FarguesFontaine/YStalks.lean:512`
- **Declarations with sorry**: none (the file is sorry-free)
- **Declarations with set_option**: none per-declaration; the file-level
  `set_option linter.overlappingInstances false` (line 28) applies to all. One declaration carries an
  `include` modifier: `tendsto_max_const_mul_pow` (`include hρ₁1 hρ₂1 in`, line 1162)
- **Proofs >30 lines**:
  - `chartDensePlus_of_exact` — 103 lines (1190–1292)
  - `mk_monomial_mem_of_le` — 92 lines (583–674)
  - `mk_monomial_pow_a_eq` — 90 lines (692–781)
  - `p_div_teich_pow_a_mem_chartSubring` — 83 lines (407–489)
  - `chartPlus_le_completedPlusSubring_of_dense` — 64 lines (270–333)
  - `mk_monomial_mem_of_large` — 63 lines (507–569)
  - `monomial_symm_blocToBI_mem_completedPlusSubring` — 61 lines (984–1044)
  - `presheafChartRingEquivBISub_symm_blocToBI` — 46 lines (800–845)
  - `exists_ball_approx` — 42 lines (211–252)
  - `completedPlusSubring_le_chartPlus` — 33 lines (151–183)
  - (also: `chartVObj`, 28 lines of instance assembly in a `def` body, 81–108)
- **TODO/FIXME comments**: none
