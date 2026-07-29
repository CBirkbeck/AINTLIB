# Inventory — `projects/AdicSpaces/Adic spaces/FarguesFontaine/Curve.lean`

The adic Fargues–Fontaine curve `𝒳 = 𝒴/φ^ℤ`: freeness and wandering of the Frobenius
action on `𝒴`, the quotient space `Curve p F ϖ`, the two-chart cover, and the point-set
theorems (T0, quasicompactness).

**Imports**: `«Adic spaces».FarguesFontaine.GaussPoint`, `«Adic spaces».FarguesFontaine.YSpace`,
`«Adic spaces».SpaQCviaSpvAI`.
**Namespace**: `FarguesFontaine`; `noncomputable section`; `universe u`;
`open TopologicalRing ValuationSpectrum Pointwise`.
**Section variables**: `(p : ℕ) [Fact p.Prime]`, `(F : Type u)` a perfectoid field of
char `p` with topological/uniform/nonarchimedean structure, `(ϖ : PseudoUniformizer F)`.

---

## Section: Freeness and wandering (`variable {p F ϖ}`)

### `theorem smul_ne_of_ne_zero`
- **Type**: `{v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) {k : ℤ} (hk : k ≠ 0) → (Multiplicative.ofAdd k) • v ≠ v`
- **What**: The `φ^ℤ`-action on `𝒴` is free: no nontrivial power of Frobenius fixes a point of `𝒴`.
- **How**: By the window covering `Y_eq_iUnion_windows`, `v` lies in some `windowU p F ϖ n`
  (or `windowV`); the translation lemma `zsmul_windowU` moves `φ^k · v` into `windowU (n - k)`,
  and `windowU_disjoint` for `n ≠ n - k` (i.e. `k ≠ 0`) contradicts `φ^k·v = v`.
- **Hypotheses**: `v ∈ Y p F ϖ` (a point of the punctured space `𝒴`); `k ≠ 0`.
- **Uses from project**: `Y`, `Ainf`, `Y_eq_iUnion_windows`, `windowU`, `windowV`,
  `zsmul_windowU`, `zsmul_windowV`, `windowU_disjoint`, `windowV_disjoint`.
- **Used by**: unused in file (stated as the headline freeness result; the injectivity lemmas
  re-derive the same argument inline).
- **Visibility**: public
- **Lines**: 68–83 (proof 15 lines)
- **Notes**: two symmetric branches (U/V), each 5 lines; no `set_option`, no `sorry`.

### `theorem exists_nhd_smul_disjoint`
- **Type**: `{v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) → ∃ W : Set (Spv (Ainf p F)), v ∈ W ∧ W ⊆ Y p F ϖ ∧ IsOpen (Subtype.val ⁻¹' W : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) ∧ ∀ k : ℤ, k ≠ 0 → Disjoint ((Multiplicative.ofAdd k) • W) W`
- **What**: The action is *wandering* (the sources' "properly discontinuous"): every point of `𝒴`
  has an open neighbourhood `W ⊆ 𝒴` moved off itself by every `φ^k`, `k ≠ 0`.
- **How**: Take `W` to be the point's own window: `Y_eq_iUnion_windows` produces `n` with
  `v ∈ windowU p F ϖ n`; openness is `isOpen_windowU`, and `zsmul_windowU` rewrites
  `φ^k • windowU n = windowU (n - k)`, which `windowU_disjoint` shows disjoint from `windowU n`.
- **Hypotheses**: `v ∈ Y p F ϖ`.
- **Uses from project**: `Y`, `Ainf`, `Spa`, `ringPlus`, `Y_eq_iUnion_windows`, `windowU`,
  `windowV`, `isOpen_windowU`, `isOpen_windowV`, `zsmul_windowU`, `zsmul_windowV`,
  `windowU_disjoint`, `windowV_disjoint`.
- **Used by**: unused in file (headline statement; consumers are downstream files).
- **Visibility**: public
- **Lines**: 90–107 (proof 14 lines)
- **Notes**: openness is stated as openness of the preimage in `Spa`, matching the ambient
  `Spa`-subtype topology convention used in `YSpace`. No `sorry`.

---

## Section: The action on the subtype `↥𝒴` (`variable (p F ϖ)`)

### `instance instContinuousConstSMulSpv`
- **Type**: `ContinuousConstSMul (Multiplicative ℤ) (Spv (Ainf p F))`
- **What**: The `φ^ℤ`-action on the valuation spectrum `Spv (Ainf p F)` is by homeomorphisms.
- **How**: Unfolds `g • v` to `comap (MulSemiringAction.toRingHom _ _ g⁻¹) v` (a `show`) and
  applies `comap_continuous`: pullback along a ring homomorphism is continuous on `Spv`.
- **Hypotheses**: the ambient perfectoid/topological structure on `F` (section variables); the
  `MulSemiringAction` of `Multiplicative ℤ` on `Ainf p F` supplied upstream.
- **Uses from project**: `Ainf`, `comap`, `comap_continuous`.
- **Used by**: `instContinuousConstSMulYSub` (via `continuous_const_smul`).
- **Visibility**: public (instance)
- **Lines**: 115–120 (proof 4 lines)
- **Notes**: the single-line `show` is genuine defeq plumbing — it respells `g • v` as a `comap`.

### `instance instMulActionYSub`
- **Type**: `MulAction (Multiplicative ℤ) ↥(Y p F ϖ)`
- **What**: The `φ^ℤ`-action restricted to the subtype `↥𝒴`, well defined because `𝒴` is
  Frobenius-stable.
- **How**: `smul g v := ⟨g • v.1, smul_mem_Y p F ϖ g v.2⟩`; the two action axioms are
  `Subtype.ext` applied to the ambient `one_smul` / `mul_smul` on `Spv (Ainf p F)`.
- **Hypotheses**: stability of `Y p F ϖ` under the action (`smul_mem_Y`).
- **Uses from project**: `Y`, `smul_mem_Y`.
- **Used by**: `instContinuousConstSMulYSub`, `Curve`, `toCurve`, and every theorem mentioning
  the orbit relation (`injOn_toCurve_windowU/V`, `curve_eq_image_window_zero`, …).
- **Visibility**: public (instance)
- **Lines**: 123–126 (structure instance, 3 fields)
- **Notes**: this is the definitional heart of the quotient — the orbit relation used by `Curve`
  is `MulAction.orbitRel` for *this* instance.

### `instance instContinuousConstSMulYSub`
- **Type**: `ContinuousConstSMul (Multiplicative ℤ) ↥(Y p F ϖ)`
- **What**: The restricted action on `↥𝒴` is by homeomorphisms for the subspace topology.
- **How**: `Continuous.subtype_mk` on the composite `continuous_const_smul g ∘ continuous_subtype_val`
  — the ambient action is continuous by `instContinuousConstSMulSpv` and the subtype inclusion is.
- **Hypotheses**: `instContinuousConstSMulSpv`, `instMulActionYSub`.
- **Uses from project**: `Y`, `instContinuousConstSMulSpv` (by instance resolution),
  `instMulActionYSub`.
- **Used by**: `isOpenQuotientMap_toCurve` (via `MulAction.isOpenQuotientMap_quotientMk`), and
  the topological results downstream (instance resolution, not by name).
- **Visibility**: public (instance)
- **Lines**: 130–133 (proof 2 lines)
- **Notes**: instance — consumed by typeclass resolution, never by name.

---

## Section: The curve

### `def Curve`
- **Type**: `(p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p] (ϖ : PseudoUniformizer F) : Type u`
  — body `Quotient (MulAction.orbitRel (Multiplicative ℤ) ↥(Y p F ϖ))`
- **What**: **The adic Fargues–Fontaine curve** `𝒳_{Q_p,F} = 𝒴/φ^ℤ`, as a topological space: the
  set-theoretic quotient of the subtype `↥(Y p F ϖ)` by the orbit equivalence relation of the
  `φ^ℤ`-action (`instMulActionYSub`). The structure presheaf is deliberately *not* part of this
  definition — it is a follow-on development.
- **How**: Direct definition as `Quotient` of `MulAction.orbitRel`; no proof content.
- **Hypotheses**: `E = Q_p` is baked in (the ring is `Ainf p F`, not a general `E`); `F` a
  perfectoid field of characteristic `p` with a chosen pseudo-uniformizer `ϖ` (which pins down the
  `𝒴 = 𝒴_{(0,∞)}` punctured region via `Y p F ϖ`).
- **Uses from project**: `Y` (and, through the `Quotient`, `instMulActionYSub` and the ambient
  `MulSemiringAction` of `Multiplicative ℤ` on `Ainf p F`).
- **Used by**: `instTopologicalSpaceCurve`, `toCurve`, `toCurve_surjective`,
  `isOpenQuotientMap_toCurve`, `injOn_toCurve_windowU`, `injOn_toCurve_windowV`,
  `curve_eq_image_window_zero`, and every result in the rest of the file.
- **Visibility**: public
- **Lines**: 142–143 (definition, 1 line of body)
- **Notes**: `Type u` — lives in the same universe as `F`. Because it is a plain `def` (not
  `abbrev`), it is semireducible: `Quotient.mk`/`Quotient.sound`/`Quotient.eq''` reasoning in this
  file goes through `toCurve` and occasionally needs the unfolding to be visible (see
  `injOn_toCurve_windowU`, which applies `Quotient.eq''.mp` directly to a `toCurve` equation).
  Sourced to [BFHHLWY, Def 2.1.1], [SW, Def 13.5.1], [Kedlaya-AWS, §3.1] in the docstring.

### `instance instTopologicalSpaceCurve`
- **Type**: `TopologicalSpace (Curve p F ϖ)`
- **What**: The curve carries the quotient topology from `↥𝒴`.
- **How**: Direct delegation to `instTopologicalSpaceQuotient`, mathlib's quotient topology on
  `Quotient s`.
- **Hypotheses**: the subspace topology on `↥(Y p F ϖ)` (inherited from `Spv (Ainf p F)`).
- **Uses from project**: `Curve`.
- **Used by**: `isOpenQuotientMap_toCurve` and all topological statements about `Curve`
  (by instance resolution).
- **Visibility**: public (instance)
- **Lines**: 145–146 (1 line)
- **Notes**: instance — consumed by resolution. Needed explicitly because `Curve` is a `def`, so
  the quotient's topology instance does not fire through the definition automatically.

### `def toCurve`
- **Type**: `↥(Y p F ϖ) → Curve p F ϖ`
- **What**: The quotient map `𝒴 → 𝒳` sending a point to its `φ^ℤ`-orbit.
- **How**: `Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) ↥(Y p F ϖ))`.
- **Hypotheses**: `[]`
- **Uses from project**: `Y`, `Curve`, `instMulActionYSub`.
- **Used by**: `toCurve_surjective`, `isOpenQuotientMap_toCurve`, `injOn_toCurve_windowU`,
  `injOn_toCurve_windowV`, `curve_eq_image_window_zero`, and the later sections.
- **Visibility**: public
- **Lines**: 149–150 (1 line)
- **Notes**: `[]`

### `theorem toCurve_surjective`
- **Type**: `Function.Surjective (toCurve p F ϖ)`
- **What**: Every point of the curve is the image of a point of `𝒴`.
- **How**: `fun c => ⟨c.out, Quotient.out_eq c⟩` — choose a representative of the quotient class.
- **Hypotheses**: `[]`
- **Uses from project**: `toCurve`, `Curve`.
- **Used by**: `curve_eq_image_window_zero` (and later T0/quasicompactness arguments).
- **Visibility**: public
- **Lines**: 152–153 (term proof, 1 line)
- **Notes**: `[]`

### `theorem isOpenQuotientMap_toCurve`
- **Type**: `IsOpenQuotientMap (toCurve p F ϖ)`
- **What**: `𝒴 → 𝒳` is an open quotient map: it is a quotient map and sends open sets to open sets.
- **How**: `MulAction.isOpenQuotientMap_quotientMk` — mathlib's general fact that the orbit map of a
  continuous group action is an open quotient map; supplied by `instContinuousConstSMulYSub`.
- **Hypotheses**: continuity of the action on `↥𝒴`.
- **Uses from project**: `toCurve`, `instContinuousConstSMulYSub` (by resolution),
  `instTopologicalSpaceCurve`.
- **Used by**: the openness/quasicompactness results later in the file.
- **Visibility**: public
- **Lines**: 157–158 (term proof, 1 line)
- **Notes**: `[]`

### `theorem injOn_toCurve_windowU`
- **Type**: `(n : ℤ) → Set.InjOn (toCurve p F ϖ) {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ n}`
- **What**: The quotient map is injective on each window `U_n` — two points of one window lying in
  the same `φ^ℤ`-orbit are equal. This is the "`U_0` maps isomorphically onto its image" statement.
- **How**: From `toCurve y₁ = toCurve y₂`, `Quotient.eq''` + `MulAction.orbitRel_apply` give
  `y₁ ∈ MulAction.orbit _ y₂`, i.e. `y₁ = g • y₂`. If `Multiplicative.toAdd g = 0` then `g = 1` and
  `y₁ = y₂`; otherwise `zsmul_windowU` places `y₁` in `windowU (n - toAdd g)`, contradicting
  `windowU_disjoint` against `y₁ ∈ windowU n`.
- **Hypotheses**: both points lie in `windowU p F ϖ n`.
- **Uses from project**: `toCurve`, `Y`, `Ainf`, `windowU`, `zsmul_windowU`, `windowU_disjoint`.
- **Used by**: unused in file (chart-injectivity API for downstream chart constructions).
- **Visibility**: public
- **Lines**: 165–182 (proof 14 lines)
- **Notes**: >10 lines; the `by_cases hk : Multiplicative.toAdd g = 0` / `rw [← ofAdd_toAdd g, hk]`
  preamble is shared verbatim with `injOn_toCurve_windowV`.

### `theorem injOn_toCurve_windowV`
- **Type**: `(n : ℤ) → Set.InjOn (toCurve p F ϖ) {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowV p F ϖ n}`
- **What**: The `V`-window analogue: `toCurve` is injective on each `V_n`.
- **How**: Verbatim the `windowU` argument with `windowV`: `Quotient.eq''` + `MulAction.orbitRel_apply`
  to get `y₁ = g • y₂`, then `zsmul_windowV` + `windowV_disjoint` to rule out `toAdd g ≠ 0`.
- **Hypotheses**: both points lie in `windowV p F ϖ n`.
- **Uses from project**: `toCurve`, `Y`, `Ainf`, `windowV`, `zsmul_windowV`, `windowV_disjoint`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 185–202 (proof 14 lines)
- **Notes**: >10 lines; a line-for-line duplicate of `injOn_toCurve_windowU` with `U ↦ V` — an
  obvious candidate for a shared private helper parameterised by the window family.

### `theorem curve_eq_image_window_zero`
- **Type**: `toCurve p F ϖ '' {y | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ 0} ∪ toCurve p F ϖ '' {y | (y.1 : Spv (Ainf p F)) ∈ windowV p F ϖ 0} = Set.univ`
- **What**: **Two charts cover the curve**: `𝒳 = im(U_0) ∪ im(V_0)`; equivalently every `φ^ℤ`-orbit
  in `𝒴` meets `U_0 ∪ V_0`.
- **How**: Given `c`, pick `y` with `toCurve y = c` (`toCurve_surjective`); `Y_eq_iUnion_windows`
  puts `y` in some `windowU n`; the local `horbit` fact (`Quotient.sound` on
  `MulAction.orbitRel_apply.mpr (MulAction.mem_orbit …)`) says `toCurve (φ^n • y) = toCurve y`, and
  `zsmul_windowU p F ϖ n n` places `φ^n • y` in `windowU (n - n) = windowU 0`.
- **Hypotheses**: `[]` (holds for all points, using the global window covering of `𝒴`).
- **Uses from project**: `toCurve`, `toCurve_surjective`, `Y`, `Ainf`, `Y_eq_iUnion_windows`,
  `windowU`, `windowV`, `zsmul_windowU`, `zsmul_windowV`.
- **Used by**: the quasicompactness argument later in the file.
- **Visibility**: public
- **Lines**: 209–239 (proof 27 lines)
- **Notes**: >10 lines (27). Contains two `show (((Multiplicative.ofAdd n) • y).1 : Spv (Ainf p F)) ∈ windowU/V p F ϖ 0`
  lines — defeq plumbing to expose the subtype coercion of the smul — plus a `simpa using this` to
  turn `n - n` into `0`. The two branches are symmetric duplicates.

### `private theorem not_vle_pow_p_zero'`
- **Type**: `{v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) (k : ℕ) → ¬ v.vle ((p : Ainf p F) ^ k) 0`
- **What**: For a point of `𝒴`, no power `p^k` is in the support of `v` (i.e. `v(p^k) ≠ 0`),
  since `v(p) ≠ 0` on `𝒴`.
- **How**: The support of a valuation is a prime ideal, so `p^k ∈ supp v` forces `p ∈ supp v`
  (`Ideal.IsPrime.mem_of_pow_mem`), contradicting `v_p_ne_zero hv`; the translation between
  `vle _ 0` and support membership is `Spv.mem_supp_iff`.
- **Hypotheses**: `v ∈ Y p F ϖ` (which is exactly where `v(p) ≠ 0` and `v(ϖ^♭) ≠ 0` hold).
- **Uses from project**: `Y`, `Ainf`, `Spv.vle`, `Spv.mem_supp_iff`, `Spv.supp`, `v_p_ne_zero`.
- **Used by**: `isOpen_windowU_Y`, `isOpen_windowV_Y`, `windowV_zero_trace_eq`.
- **Visibility**: private
- **Lines**: 241–244 (term proof, 4 lines)
- **Notes**: uses `(inferInstance : (v.supp).IsPrime)` to get primality of the support.

### `private theorem not_vle_pow_teichPi_zero'`
- **Type**: `{v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) (k : ℕ) → ¬ v.vle (teichPi p F ϖ ^ k) 0`
- **What**: The Teichmüller-lift analogue: for a point of `𝒴`, `v([ϖ]^k) ≠ 0`.
- **How**: Same primality argument as `not_vle_pow_p_zero'` — `Ideal.IsPrime.mem_of_pow_mem` on
  `supp v` reduces to `v_teichPi_ne_zero hv`, mediated by `Spv.mem_supp_iff`.
- **Hypotheses**: `v ∈ Y p F ϖ`.
- **Uses from project**: `Y`, `Ainf`, `teichPi`, `Spv.vle`, `Spv.mem_supp_iff`, `Spv.supp`,
  `v_teichPi_ne_zero`.
- **Used by**: `isOpen_windowU_Y`, `isOpen_windowV_Y`, `windowU_zero_trace_eq`,
  `windowV_zero_trace_eq`.
- **Visibility**: private
- **Lines**: 246–249 (term proof, 4 lines)
- **Notes**: structurally identical to `not_vle_pow_p_zero'` (candidate for a shared helper on a
  generic non-support element).

### `private theorem isOpen_windowU_Y`
- **Type**: `(n : ℤ) → IsOpen {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ n}`
- **What**: The trace of the window `U_n` on the subtype `↥𝒴` is open in the subspace topology.
- **How**: Rewrites the window as an intersection of two preimages of `ValuationSpectrum.basicOpen`
  sets — `basicOpen ([ϖ]^den) (p^num)` and `basicOpen (p^num) ([ϖ]^den)` for the exponents
  `((p:ℚ)^n)` and `cFF p * (p:ℚ)^n` — the `Y`-membership component being supplied by
  `not_vle_pow_p_zero'` / `not_vle_pow_teichPi_zero'`; then `isOpen_basicOpen` plus
  `continuous_subtype_val.isOpen_preimage` and `IsOpen.inter`.
- **Hypotheses**: implicit — the points live in `↥(Y p F ϖ)`, which is what makes the extra
  "nonvanishing" side conditions of `basicOpen` free.
- **Uses from project**: `Y`, `Ainf`, `windowU`, `KGE`, `KLE`, `teichPi`, `cFF`, `basicOpen`,
  `isOpen_basicOpen`, `not_vle_pow_p_zero'`, `not_vle_pow_teichPi_zero'`.
- **Used by**: `instT0SpaceCurve` (twice: the openness of the `U_0`-image and the `sep_of_chart` call).
- **Visibility**: private
- **Lines**: 251–266 (proof 15 lines)
- **Notes**: >10 lines; the bulk is the `heq` set equation — a `simp only [… windowU, basicOpen,
  KGE, KLE]` unfolding followed by an explicit anonymous-constructor bi-implication. This is
  *unfolding/plumbing*, not mathematical content.

### `private theorem isOpen_windowV_Y`
- **Type**: `(n : ℤ) → IsOpen {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowV p F ϖ n}`
- **What**: Same for the `V`-windows: the trace of `V_n` on `↥𝒴` is open.
- **How**: Identical to `isOpen_windowU_Y` with the two exponents `cFF p * (p:ℚ)^n` and
  `(p:ℚ)^(n+1)`: express as an intersection of two `basicOpen` preimages, discharge the support
  side conditions with `not_vle_pow_p_zero'` / `not_vle_pow_teichPi_zero'`, conclude by
  `isOpen_basicOpen`.
- **Hypotheses**: as above.
- **Uses from project**: `Y`, `Ainf`, `windowV`, `KGE`, `KLE`, `teichPi`, `cFF`, `basicOpen`,
  `isOpen_basicOpen`, `not_vle_pow_p_zero'`, `not_vle_pow_teichPi_zero'`.
- **Used by**: `instT0SpaceCurve`.
- **Visibility**: private
- **Lines**: 268–283 (proof 15 lines)
- **Notes**: >10 lines; verbatim duplicate of `isOpen_windowU_Y` apart from the two rational
  exponents. The final 3-line `rw [heq]; exact (…).inter (…)` tail is byte-identical in both.

### `private theorem sep_of_chart`
- **Type**: `{S : Set ↥(Y p F ϖ)} (hSopen : IsOpen S) (hinj : Set.InjOn (toCurve p F ϖ) S) {z₁ z₂ : ↥(Y p F ϖ)} (h₁ : z₁ ∈ S) (h₂ : z₂ ∈ S) (hne : toCurve p F ϖ z₁ ≠ toCurve p F ϖ z₂) → ∃ C : Set (Curve p F ϖ), IsOpen C ∧ Xor (toCurve p F ϖ z₁ ∈ C) (toCurve p F ϖ z₂ ∈ C)`
- **What**: T0-separation transported through a chart: if two points of `𝒴` lie in a common open
  set `S` on which `toCurve` is injective, and their images differ, then some open set of the curve
  contains exactly one of the two images.
- **How**: `z₁ ≠ z₂` (else images agree), so T0-ness of `↥𝒴` (inherited from `Spa`, obtained via
  `t0Space_iff_exists_isOpen_xor_mem` + `inferInstance`) gives an open `O` separating them; push
  `S ∩ O` forward, open by `(isOpenQuotientMap_toCurve …).isOpenMap`. Injectivity `hinj` on `S`
  shows the *other* point's image cannot be in the image, since any preimage `w ∈ S ∩ O` with
  `toCurve w = toCurve z₂` must equal `z₂`.
- **Hypotheses**: `S` open, `toCurve` injective on `S`, both points in `S`, images distinct.
- **Uses from project**: `Y`, `toCurve`, `Curve`, `isOpenQuotientMap_toCurve`.
- **Used by**: `instT0SpaceCurve` (both branches — the `U_0` and the `V_0` chart).
- **Visibility**: private
- **Lines**: 285–303 (proof 14 lines)
- **Notes**: >10 lines; the two `rcases` branches are mirror images (swap `z₁`/`z₂`), each 5 lines.
  This is the file's one genuinely-shared helper — it is why `instT0SpaceCurve` stays short.

### `instance instT0SpaceCurve`
- **Type**: `T0Space (Curve p F ϖ)`
- **What**: The curve is a T0 topological space.
- **How**: `t0Space_iff_exists_isOpen_xor_mem`; the two-chart cover
  `curve_eq_image_window_zero` puts each of `c₁, c₂` in `im(U_0)` or `im(V_0)`. If both lie in
  `im(U_0)` (resp. neither, hence both in `im(V_0)`) apply `sep_of_chart` with
  `isOpen_windowU_Y`/`injOn_toCurve_windowU` (resp. the `V` versions); if exactly one lies in
  `im(U_0)`, that image itself is the separating open set (open by
  `(isOpenQuotientMap_toCurve …).isOpenMap`).
- **Hypotheses**: T0-ness of `Spa (Ainf p F) (ringPlus (Ainf p F))` (supplied upstream by
  instance resolution), plus the window machinery.
- **Uses from project**: `Curve`, `toCurve`, `Y`, `Ainf`, `windowU`, `curve_eq_image_window_zero`,
  `isOpenQuotientMap_toCurve`, `isOpen_windowU_Y`, `isOpen_windowV_Y`, `injOn_toCurve_windowU`,
  `injOn_toCurve_windowV`, `sep_of_chart`.
- **Used by**: unused in file (instance — consumed by typeclass resolution downstream).
- **Visibility**: public (instance)
- **Lines**: 307–326 (proof 19 lines)
- **Notes**: >10 lines; four-way `by_cases` on chart membership, hence the length. No `set_option`,
  no `sorry`.

### `private theorem mem_rationalOpen_pair_iff`
- **Type**: `{v : Spv (Ainf p F)} (hv : v ∈ Spa (Ainf p F) (ringPlus (Ainf p F))) {t₁ s₁ t₂ s₂ : Ainf p F} → v ∈ rationalOpen {t₁*t₂, t₁*s₂, s₁*t₂, s₁*s₂} (s₁*s₂) ↔ (v.vle t₁ s₁ ∧ ¬ v.vle s₁ 0) ∧ (v.vle t₂ s₂ ∧ ¬ v.vle s₂ 0)`
- **What**: **The two-condition-to-rational-subset engine** (Wedhorn Rem. 7.30(5)): on `Spa`, a
  conjunction of two "`v(tᵢ) ≤ v(sᵢ) ≠ 0`" conditions is exactly membership in the rational
  subset with numerator set `{t₁t₂, t₁s₂, s₁t₂, s₁s₂}` and denominator `s₁s₂`.
- **How**: (⇒) `¬ v.vle (s₁s₂) 0` forces each `¬ v.vle sᵢ 0` via `Spv.mul_vle_mul_left` and
  `zero_mul`; the individual inequalities come from `Spv.vle_mul_cancel` applied to
  `v.vle (t₁s₂) (s₁s₂)` and `v.vle (s₁t₂) (s₁s₂)`. (⇐) a local `hmul` lemma
  (`vle_trans` + two `mul_vle_mul_left`) checks all four generators against `s₁s₂`, and
  primality of `Spv.supp` (`Ideal.IsPrime.mem_or_mem` + `Spv.mem_supp_iff`) rules out
  `v.vle (s₁s₂) 0`.
- **Hypotheses**: `v ∈ Spa (Ainf p F) (ringPlus (Ainf p F))` (needed only to rebuild the
  `rationalOpen` membership in the ⇐ direction); no hypothesis on `tᵢ, sᵢ`.
- **Uses from project**: `Ainf`, `Spa`, `ringPlus`, `rationalOpen`, `Spv.vle`, `Spv.supp`,
  `Spv.mem_supp_iff`, `Spv.mul_vle_mul_left`, `Spv.vle_mul_cancel`, `Spv.vle_trans`,
  `Spv.vle_total`.
- **Used by**: `windowU_zero_trace_eq`, `windowV_zero_trace_eq` (both open with
  `rw [mem_rationalOpen_pair_iff p F v.2]`).
- **Visibility**: private
- **Lines**: 332–370 (proof 34 lines)
- **Notes**: >30 lines (34). `open Classical in`. The longest proof in the file so far and the only
  one that is long for *mathematical* reasons (valuation-axiom manipulation), not plumbing. The
  reflexivity witnesses `hrefl₁/hrefl₂` are obtained as `(v.vle_total s s).elim id id`.

### `private theorem cFF_num_toNat_pos`
- **Type**: `0 < (cFF p).num.toNat`
- **What**: The numerator of the Fargues–Fontaine constant `cFF p` is a positive natural number.
- **How**: `one_lt_cFF` (using `p` prime, so `1 < p`) gives `0 < cFF p`, hence `0 < (cFF p).num`
  by `Rat.num_pos`, and `omega` converts to `Int.toNat`.
- **Hypotheses**: `[Fact (Nat.Prime p)]` (used as `(Fact.out : Nat.Prime p).one_lt`).
- **Uses from project**: `cFF`, `one_lt_cFF`.
- **Used by**: `windowV_zero_trace_eq` (positivity of the `Ideal.pow_mem_of_mem` exponent).
- **Visibility**: private
- **Lines**: 372–376 (proof 4 lines)
- **Notes**: `[]`

### `private theorem windowU_zero_trace_eq`
- **Type**: `(Subtype.val ⁻¹' windowU p F ϖ 0 : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) = Subtype.val ⁻¹' rationalOpen {[ϖ]·p^(cFF p).num.toNat, [ϖ]·[ϖ]^(cFF p).den, p·p^(cFF p).num.toNat, p·[ϖ]^(cFF p).den} (p·[ϖ]^(cFF p).den)`
- **What**: The chart `U_0`, traced on `Spa`, *is* a rational subset — explicitly exhibited with
  numerator set `{t₁t₂, t₁s₂, s₁t₂, s₁s₂}` for `t₁ = [ϖ]`, `s₁ = p`, `t₂ = p^(cFF p).num.toNat`,
  `s₂ = [ϖ]^(cFF p).den`. This is what makes `U_0` affinoid (hence quasicompact).
- **How**: `mem_rationalOpen_pair_iff` reduces the RHS to the two `vle` conditions; two `have`s
  specialise `KGE`/`KLE` at `n = 0` (`zpow_zero`, `Rat.den_one`, `Rat.num_one`, `Int.toNat_one`,
  `pow_one`), and the `Y`-membership component of `windowU` is recovered from the nonvanishing
  conditions using primality of `Spv.supp` (`Ideal.IsPrime.mem_or_mem`, `Ideal.pow_mem_of_mem`
  with `(cFF p).den_pos`) together with `v_p_ne_zero` / `not_vle_pow_teichPi_zero'`.
- **Hypotheses**: none beyond the section variables; the `Spa`-membership `v.2` of the subtype is
  what feeds `mem_rationalOpen_pair_iff`.
- **Uses from project**: `windowU`, `Y`, `Ainf`, `Spa`, `ringPlus`, `rationalOpen`, `teichPi`,
  `cFF`, `KGE`, `KLE`, `Spv.vle`, `Spv.supp`, `Spv.mem_supp_iff`, `mem_rationalOpen_pair_iff`,
  `v_p_ne_zero`, `not_vle_pow_teichPi_zero'`.
- **Used by**: `isCompact_windowU_zero`.
- **Visibility**: private
- **Lines**: 379–412 (proof 25 lines)
- **Notes**: >10 lines. `open Classical in`. Long because the numerator/denominator data is spelled
  out and both `KGE`/`KLE` need `n = 0` normalisation — plumbing, not new mathematics.

### `private theorem windowV_zero_trace_eq`
- **Type**: `(Subtype.val ⁻¹' windowV p F ϖ 0 : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) = Subtype.val ⁻¹' rationalOpen {[ϖ]^(cFF p).den · p^(p:ℚ).num.toNat, [ϖ]^(cFF p).den · [ϖ]^(p:ℚ).den, p^(cFF p).num.toNat · p^(p:ℚ).num.toNat, p^(cFF p).num.toNat · [ϖ]^(p:ℚ).den} (p^(cFF p).num.toNat · [ϖ]^(p:ℚ).den)`
- **What**: The chart `V_0`, traced on `Spa`, is a rational subset, exhibited explicitly with
  `t₁ = [ϖ]^(cFF p).den`, `s₁ = p^(cFF p).num.toNat`, `t₂ = p^(p:ℚ).num.toNat`,
  `s₂ = [ϖ]^(p:ℚ).den` — the `V`-analogue of `windowU_zero_trace_eq`.
- **How**: `mem_rationalOpen_pair_iff` turns the RHS into two `vle` conditions; `hKGE`/`hKLE`
  specialise `KGE` at `cFF p · p^0 = cFF p` and `KLE` at `p^(0+1) = p` (`zpow_zero`, `mul_one`,
  `zero_add`, `zpow_one`); the `Y`-membership is rebuilt from primality of `Spv.supp` via
  `Ideal.IsPrime.mem_or_mem` and `Ideal.pow_mem_of_mem`, with positivity of the exponents supplied
  by `cFF_num_toNat_pos` and `Rat.den_natCast` + `omega`.
- **Hypotheses**: none beyond section variables; `v.2` (the `Spa`-membership) feeds
  `mem_rationalOpen_pair_iff`.
- **Uses from project**: `windowV`, `Y`, `Ainf`, `Spa`, `ringPlus`, `rationalOpen`, `teichPi`,
  `cFF`, `KGE`, `KLE`, `Spv.vle`, `Spv.supp`, `Spv.mem_supp_iff`, `mem_rationalOpen_pair_iff`,
  `cFF_num_toNat_pos`, `not_vle_pow_p_zero'`, `not_vle_pow_teichPi_zero'`.
- **Used by**: `isCompact_windowV_zero`.
- **Visibility**: private
- **Lines**: 415–451 (proof 28 lines)
- **Notes**: >10 lines. `open Classical in`. Near-verbatim twin of `windowU_zero_trace_eq`
  (differs only in the two rational exponents and in which positivity fact discharges
  `Ideal.pow_mem_of_mem`) — the shared skeleton `ext v; simp only [Set.mem_preimage];
  rw [mem_rationalOpen_pair_iff p F v.2]; have hKGE …; have hKLE …; constructor` runs across both.

### `private theorem ainf_pair_spec`
- **Type**: `∃ P : PairOfDefinition (Ainf p F), ∃ g₁ g₂ : P.A₀, P.I = Ideal.span {g₁, g₂} ∧ (∀ x : P.A₀, (x : Ainf p F) ∈ (ringPlus (Ainf p F) : Subring (Ainf p F))) ∧ Iinf p F (IsTateRing.pseudoUniformizer (A := F)) = Ideal.span {(g₁ : Ainf p F), (g₂ : Ainf p F)}`
- **What**: Packages `A_inf` as a *pair of definition* whose ideal of definition is generated by
  the two elements `p` and `[ϖ]`, with `A₀` contained in the integral subring `ringPlus`. This is
  the input the quasicompactness engine needs.
- **How**: Witness `P := pairOfDefinition_ofAdic (Iinf p F …)` (finitely generated by
  `Submodule.fg_span (Set.toFinite _)`), with `g₁ = p`, `g₂ = teichPi p F …`; `A₀ = ⊤` so the
  containment is `trivial`. The ideal equation is a `show idealToTop … = _` plus
  `Ideal.map_span`, `Set.image_insert_eq`, `Set.image_singleton`, closing by `rfl`.
- **Hypotheses**: `A_inf` adic with `Iinf` its ideal of definition; the pseudo-uniformizer is the
  canonical `IsTateRing.pseudoUniformizer (A := F)` (not the section's `ϖ`).
- **Uses from project**: `Ainf`, `PairOfDefinition`, `pairOfDefinition_ofAdic`, `ringPlus`,
  `Iinf`, `teichPi`, `idealToTop`.
- **Used by**: `isCompact_windowU_zero`, `isCompact_windowV_zero`.
- **Visibility**: private
- **Lines**: 457–474 (proof 12 lines)
- **Notes**: >10 lines and *pure defeq plumbing*: two `show`/`rw [show … from rfl]` blocks
  respelling the elaborated `idealToTop` term, then `rfl`. No mathematical content beyond choosing
  the generators.

### `private theorem iinf_le_radical_of_pure_powers`
- **Type**: `{T : Finset (Ainf p F)} (hp : ∃ n : ℕ, (p : Ainf p F) ^ n ∈ T) (hϖ : ∃ m : ℕ, 0 < m ∧ teichPi p F ϖ ^ m ∈ T) → Iinf p F (IsTateRing.pseudoUniformizer (A := F)) ≤ (Ideal.span (T : Set (Ainf p F))).radical`
- **What**: If a finite set `T` contains some pure power of `p` and some *positive* pure power of
  `[ϖ]`, then the ideal of definition `Iinf = (p, [ϖ_canonical])` lies in the radical of `span T`
  — the "the numerators of the rational subset generate an open ideal" condition.
- **How**: `Iinf` is `span {p, [ϖ_canon]}`, so `Ideal.span_le` reduces to the two generators. For
  `p` take the exponent from `hp` directly. For the Teichmüller lift, transfer the *canonical*
  pseudo-uniformizer to `ϖ` via `exists_teichPi_pow_mem_span_teichPi` (giving
  `[ϖ_canon]^k = c · [ϖ]` through `Ideal.mem_span_singleton'`), then `pow_mul` + `mul_pow` gives
  `[ϖ_canon]^(k·m) = c^m · [ϖ]^m ∈ span T` by `Ideal.mul_mem_left`.
- **Hypotheses**: `T` contains a power of `p` and a positive power of `teichPi p F ϖ` — positivity
  of `m` is essential (`m = 0` would give only `1`).
- **Uses from project**: `Ainf`, `Iinf`, `teichPi`, `exists_teichPi_pow_mem_span_teichPi`.
- **Used by**: `isCompact_windowU_zero`, `isCompact_windowV_zero`.
- **Visibility**: private
- **Lines**: 476–494 (proof 14 lines)
- **Notes**: >10 lines; the substantive step is the uniformizer-comparison
  `exists_teichPi_pow_mem_span_teichPi`, which is what lets an arbitrary `ϖ` stand in for the
  canonical Tate pseudo-uniformizer used by `Iinf`.

### `theorem isCompact_windowU_zero`
- **Type**: `IsCompact (Subtype.val ⁻¹' windowU p F ϖ 0 : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))`
- **What**: The chart `U_0` is quasicompact in `Spa(A_inf, A_inf^+)` — it is an affinoid
  (rational) subset.
- **How**: Rewrite `U_0` as a rational subset (`windowU_zero_trace_eq`), then apply the engine
  `isCompact_subtype_rationalOpen₂` with the pair of definition from `ainf_pair_spec`; its openness
  side condition is `iinf_le_radical_of_pure_powers` with exponents `1 + (cFF p).num.toNat` for `p`
  and `1 + (cFF p).den` for `[ϖ]` (positive, hence the `by omega`), matched to the numerator set by
  `pow_add`/`pow_one` + `simp`.
- **Hypotheses**: `[]` beyond section variables.
- **Uses from project**: `windowU`, `Ainf`, `Spa`, `ringPlus`, `windowU_zero_trace_eq`,
  `ainf_pair_spec`, `iinf_le_radical_of_pure_powers`, `isCompact_subtype_rationalOpen₂`, `cFF`.
- **Used by**: `instCompactSpaceCurve`.
- **Visibility**: public
- **Lines**: 496–508 (proof 9 lines)
- **Notes**: `classical`. The exponents are `1 + …` rather than `…` because the numerator-set
  elements from `windowU_zero_trace_eq` are `p · p^(cFF p).num.toNat` and `p · [ϖ]^(cFF p).den`.

### `theorem isCompact_windowV_zero`
- **Type**: `IsCompact (Subtype.val ⁻¹' windowV p F ϖ 0 : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))`
- **What**: The chart `V_0` is quasicompact — the `V`-analogue of `isCompact_windowU_zero`.
- **How**: Same route: `windowV_zero_trace_eq` presents `V_0` as a rational subset, then
  `isCompact_subtype_rationalOpen₂` with `ainf_pair_spec`, the radical condition supplied by
  `iinf_le_radical_of_pure_powers` at exponents `(cFF p).num.toNat + (p:ℚ).num.toNat` and
  `(cFF p).den + (p:ℚ).den` (`positivity`), matched by `pow_add` + `simp`.
- **Hypotheses**: `[]` beyond section variables.
- **Uses from project**: `windowV`, `Ainf`, `Spa`, `ringPlus`, `windowV_zero_trace_eq`,
  `ainf_pair_spec`, `iinf_le_radical_of_pure_powers`, `isCompact_subtype_rationalOpen₂`, `cFF`.
- **Used by**: `instCompactSpaceCurve`.
- **Visibility**: public
- **Lines**: 511–524 (proof 10 lines)
- **Notes**: structurally identical to `isCompact_windowU_zero` (same 4-line opening
  `classical; rw [..._trace_eq]; obtain ⟨P, g₁, g₂, hpair, hA₀le, hIeq⟩ := ainf_pair_spec p F;
  refine isCompact_subtype_rationalOpen₂ …`).

### `instance instCompactSpaceCurve`
- **Type**: `CompactSpace (Curve p F ϖ)`
- **What**: **The curve is quasicompact**: `𝒳` is covered by the images of the two quasicompact
  charts `U_0` and `V_0`, so it is compact (Kedlaya-AWS Rem. 3.1.9: "X_S can be covered by two
  affinoid subspaces").
- **How**: Transport compactness down two subtype layers: `Subtype.image_preimage_coe` +
  `Set.inter_eq_right` (using that `windowU ⊆ Spa` and `windowU ⊆ Y`) converts
  `isCompact_windowU_zero` into compactness of `windowU p F ϖ 0` in `Spv`, then of its trace in
  `↥(Y p F ϖ)` via `Topology.IsEmbedding.subtypeVal.isCompact_iff`. Finally `isCompact_univ_iff`
  and `curve_eq_image_window_zero` rewrite `univ` as the union of the two images, compact as
  continuous images (`(isOpenQuotientMap_toCurve …).continuous`) by `IsCompact.union`.
- **Hypotheses**: `[]` beyond section variables (the two chart-compactness results and the cover).
- **Uses from project**: `Curve`, `Y`, `Ainf`, `Spa`, `ringPlus`, `windowU`, `windowV`,
  `isCompact_windowU_zero`, `isCompact_windowV_zero`, `curve_eq_image_window_zero`,
  `isOpenQuotientMap_toCurve`.
- **Used by**: unused in file (instance — consumed by typeclass resolution).
- **Visibility**: public (instance)
- **Lines**: 531–570 (proof 39 lines)
- **Notes**: >30 lines (39) and the longest proof in the file. Length is almost entirely
  **subtype-coercion plumbing**: four nearly identical `have` blocks (`hWU`/`hWV` and `hSU`/`hSV`)
  each doing `Subtype.image_preimage_coe` + `Set.inter_eq_right.mpr (fun v hv => hv.1(.1))`, plus
  two `rw [show {y | …} = (Subtype.val ⁻¹' … : Set ↥(Y p F ϖ)) from rfl, …]` defeq respellings.
  The actual mathematics is the last two lines. Prime candidate for a `Set`-level helper lemma.

### `theorem Y_nonempty`
- **Type**: `(Y p F ϖ).Nonempty`
- **What**: **The curve is nonempty** (equivalently `𝒴 ≠ ∅`): the `ρ = 1/2` Gauss point
  `w_ρ(Σ pⁿ[aₙ]) = sup ρⁿ|aₙ|` is a continuous multiplicative valuation on `A_inf` with
  `w(p·[ϖ]) = ρ·|ϖ| ≠ 0`.
- **How**: Direct delegation to `Y_nonempty'` from `GaussPoint.lean`, where the Gauss-point
  construction and its multiplicativity (Kedlaya 1004.0466, Lemma 4.1) are carried out.
- **Hypotheses**: `[]` beyond section variables.
- **Uses from project**: `Y`, `Y_nonempty'`.
- **Used by**: unused in file (re-export for downstream consumers).
- **Visibility**: public
- **Lines**: 576 (term proof, 1 line)
- **Notes**: a pure re-export/alias of `Y_nonempty'`; a cleanup candidate (either drop it or give
  it a `@[simp]`-free deprecation-style pointer).

---

### File Summary

**Totals.** **29 declarations** in `namespace FarguesFontaine` (`2 defs + 21 theorems + 6 instances`;
no `structure`, `class`, or `abbrev`; note a grep for `^structure` false-positives on line 138,
which is prose inside the `Curve` docstring):
- **2 defs** — `Curve` (the carrier) and `toCurve` (the quotient map).
- **21 theorems**, 10 public + 11 private: public — `smul_ne_of_ne_zero`, `exists_nhd_smul_disjoint`,
  `toCurve_surjective`, `isOpenQuotientMap_toCurve`, `injOn_toCurve_windowU`,
  `injOn_toCurve_windowV`, `curve_eq_image_window_zero`, `isCompact_windowU_zero`,
  `isCompact_windowV_zero`, `Y_nonempty`; private — `not_vle_pow_p_zero'`,
  `not_vle_pow_teichPi_zero'`, `isOpen_windowU_Y`, `isOpen_windowV_Y`, `sep_of_chart`,
  `mem_rationalOpen_pair_iff`, `cFF_num_toNat_pos`, `windowU_zero_trace_eq`,
  `windowV_zero_trace_eq`, `ainf_pair_spec`, `iinf_le_radical_of_pure_powers`
  (**10 public + 11 private = 21 theorems**).
- **6 instances**: `instContinuousConstSMulSpv`, `instMulActionYSub`,
  `instContinuousConstSMulYSub`, `instTopologicalSpaceCurve`, `instT0SpaceCurve`,
  `instCompactSpaceCurve`.
- **No** `structure`, `class`, or `abbrev`.
- Precise count: **2 defs + 21 theorems + 6 instances = 29 declarations.**

**Key API used by 3+ in-file consumers.**
- `Curve` — used by 10+ declarations (every statement about the quotient).
- `toCurve` — used by 7 (`toCurve_surjective`, `isOpenQuotientMap_toCurve`, both `injOn_*`,
  `curve_eq_image_window_zero`, `sep_of_chart`, `instT0SpaceCurve`).
- `Y` / `Ainf` / `Spa` / `ringPlus` — pervasive (every statement).
- `windowU` / `windowV`, `zsmul_windowU` / `zsmul_windowV`, `windowU_disjoint` /
  `windowV_disjoint` (from `YSpace.lean`) — each used by 3–5 declarations.
- `Y_eq_iUnion_windows` — 3 consumers (`smul_ne_of_ne_zero`, `exists_nhd_smul_disjoint`,
  `curve_eq_image_window_zero`).
- `isOpenQuotientMap_toCurve` — 3 consumers (`sep_of_chart`, `instT0SpaceCurve`,
  `instCompactSpaceCurve`).
- `not_vle_pow_p_zero'` / `not_vle_pow_teichPi_zero'` — 3–4 consumers each
  (`isOpen_windowU_Y`, `isOpen_windowV_Y`, `windowU_zero_trace_eq`, `windowV_zero_trace_eq`).
- `mem_rationalOpen_pair_iff`, `ainf_pair_spec`, `iinf_le_radical_of_pure_powers` — 2 each
  (the `U`/`V` pair).

**Unused declarations (no in-file consumer).**
- `smul_ne_of_ne_zero` — plain `theorem`, not an instance/`@[simp]`. **Genuinely unconsumed
  in-file**, but it is the file's headline freeness statement and is intended as public API;
  note that `injOn_toCurve_windowU/V` re-derive the same argument inline instead of calling it —
  a real refactoring opportunity, not dead code.
- `exists_nhd_smul_disjoint` — plain `theorem`, headline "properly discontinuous" statement,
  public API for downstream files.
- `Y_nonempty` — plain `theorem`, a re-export of `Y_nonempty'`; unconsumed in-file by design.
- `instT0SpaceCurve`, `instCompactSpaceCurve` — **instances**: consumed by typeclass resolution,
  **not dead**. (`instTopologicalSpaceCurve`, `instContinuousConstSMulSpv`,
  `instContinuousConstSMulYSub`, `instMulActionYSub` are also instances *and* have in-file
  consumers.)
- No `@[simp]` lemmas are declared in this file, so nothing here is "consumed by the simp set".
- Everything else (`toCurve_surjective`, `isOpenQuotientMap_toCurve`, both `injOn_toCurve_window*`,
  `curve_eq_image_window_zero`, both `isCompact_window*_zero`, and all 11 private lemmas) has at
  least one in-file consumer.

**Declarations with `sorry`.** None. The file is sorry-free.

**Declarations with `set_option`.** None — no `maxHeartbeats`, no `maxRecDepth`, no linter
options anywhere in the file. Three declarations carry `open Classical in`
(`mem_rationalOpen_pair_iff`, `windowU_zero_trace_eq`, `windowV_zero_trace_eq`) and two use the
`classical` tactic (`isCompact_windowU_zero`, `isCompact_windowV_zero`).

**Proofs >30 lines** — **2**:
1. `instCompactSpaceCurve`, 39 lines (531–570).
2. `mem_rationalOpen_pair_iff`, 34 lines (332–370).

Proofs in the 20–30 line band (**3**): `curve_eq_image_window_zero` (27),
`windowV_zero_trace_eq` (28), `windowU_zero_trace_eq` (25). Proofs 10–20 lines (**10**):
`smul_ne_of_ne_zero`, `exists_nhd_smul_disjoint`, `injOn_toCurve_windowU`,
`injOn_toCurve_windowV`, `isOpen_windowU_Y`, `isOpen_windowV_Y`, `sep_of_chart`,
`instT0SpaceCurve`, `ainf_pair_spec`, `iinf_le_radical_of_pure_powers`.

---

### (a) Verbatim-repeated proof preambles

The file is built almost entirely out of **U/V twin pairs**, so repetition is structural rather
than incidental. Blocks repeated **verbatim** (up to `U ↦ V`):

1. **The orbit-triviality preamble** — 6 lines, appears **twice verbatim** in
   `injOn_toCurve_windowU` and `injOn_toCurve_windowV`:
   ```
   intro y₁ h₁ y₂ h₂ heq
   have hrel : y₁ ∈ MulAction.orbit (Multiplicative ℤ) y₂ :=
     MulAction.orbitRel_apply.mp (Quotient.eq''.mp heq)
   obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hrel
   by_cases hk : Multiplicative.toAdd g = 0
   · have hg1 : g = 1 := by rw [← ofAdd_toAdd g, hk]; rfl
     rw [hg1, one_smul] at hg; exact hg.symm
   ```
   Only 2 occurrences — below the "3+" bar, but the two proofs are otherwise identical too.

2. **The `basicOpen`-intersection tail** — the 3-line
   `rw [heq]; exact (continuous_subtype_val.isOpen_preimage _ (isOpen_basicOpen _ _)).inter (…)`
   plus the `exact ⟨fun ⟨_, h1, h2⟩ => ⟨⟨h1, not_vle_pow_p_zero' …⟩, ⟨h2, not_vle_pow_teichPi_zero' …⟩⟩,
   fun ⟨⟨h1, _⟩, ⟨h2, _⟩⟩ => ⟨y.2, h1, h2⟩⟩` bi-implication — **byte-identical** in
   `isOpen_windowU_Y` and `isOpen_windowV_Y` (2 occurrences).

3. **The trace-equation opening** — `ext v; simp only [Set.mem_preimage];
   rw [mem_rationalOpen_pair_iff p F v.2]` followed by the two `have hKGE`/`have hKLE`
   normalisations and the `constructor`-plus-`rintro ⟨hY, hge, hle⟩` skeleton: identical in
   `windowU_zero_trace_eq` and `windowV_zero_trace_eq` (2 occurrences). The `hY` reconstruction
   block (`have hprime := inferInstance; refine ⟨v.2, fun h0 => ?_⟩; rcases hprime.mem_or_mem …`)
   is likewise a verbatim twin.

4. **The compactness opening** — `classical; rw [window*_zero_trace_eq];
   obtain ⟨P, g₁, g₂, hpair, hA₀le, hIeq⟩ := ainf_pair_spec p F;
   refine isCompact_subtype_rationalOpen₂ P hpair hA₀le _ hIeq _ _ ?_` — identical in
   `isCompact_windowU_zero` and `isCompact_windowV_zero` (2 occurrences).

5. **The only genuine 3+ repetition** is the one-liner
   `Set.inter_eq_right.mpr (fun v hv => hv.1)` / `(fun v hv => hv.1.1)` following
   `rw [Subtype.image_preimage_coe]` — it occurs **4 times inside `instCompactSpaceCurve`
   alone** (`hWU`, `hWV`, `hSU`, `hSV`).

**Verdict on (a):** no preamble is repeated in 3+ *separate declarations*, but every non-trivial
result exists as a `U`/`V` pair whose proofs are line-for-line duplicates, and one proof
(`instCompactSpaceCurve`) repeats the same 3-line subtype-coercion block 4 times internally.
Extracting (i) a window-family-generic helper (parameterised over `windowU`/`windowV`) and
(ii) a `Set`-level `Subtype.image_preimage` lemma would roughly halve the file.

### (b) Are the long proofs long because of DEFEQ PLUMBING?

**Yes — this file is predominantly a DEFEQ-PLUMBING file, with one exception.**

- **`instCompactSpaceCurve` (39 lines)** — the clearest case. Its four `have` blocks exist purely
  to move a compact set between three nested subtype presentations (`Set ↥(Spa …)` →
  `Set (Spv …)` → `Set ↥(Y …)`), and it contains **two explicit
  `rw [show {y : ↥(Y p F ϖ) | (y.1 : Spv (Ainf p F)) ∈ windowU p F ϖ 0} = (Subtype.val ⁻¹' windowU p F ϖ 0 : Set ↥(Y p F ϖ)) from rfl, …]`**
  respellings — a multi-line `show … from rfl` restating an elaborated term. The mathematics is
  the final two lines.
- **`ainf_pair_spec` (12 lines)** — almost 100% plumbing: `show idealToTop … = _` followed by a
  multi-line `rw [show idealToTop … = Ideal.map (Subring.topEquiv …).symm.toRingHom (Ideal.span {…}) from rfl, …]`
  and closing `rfl`/`rfl`.
- **`windowU_zero_trace_eq` / `windowV_zero_trace_eq` (25/28 lines)** — long because `KGE`/`KLE`
  must be normalised at `n = 0` via `rw [show ((p:ℚ)^(0:ℤ)) = 1 from zpow_zero _, …]` and because
  the four-element numerator set is written out; the `Y`-membership reconstruction is real but
  short.
- **`isOpen_windowU_Y` / `isOpen_windowV_Y` (15 lines each)** — the `heq` set equation is an
  unfolding of `windowU`/`basicOpen`/`KGE`/`KLE` into an anonymous-constructor bi-implication:
  plumbing.
- **`instContinuousConstSMulSpv`** — a one-line `show` respelling `g • v` as a `comap`.

**The exception:** `mem_rationalOpen_pair_iff` (34 lines) is long for genuine **mathematical**
reasons — it is a real valuation-theoretic argument (`mul_vle_mul_left`, `vle_mul_cancel`,
`vle_trans`, `vle_total`, primality of the support) with no `show`-respelling at all. Likewise
`iinf_le_radical_of_pure_powers` and `sep_of_chart` are honest short proofs.

**Summary for Phase 4:** `Curve.lean` is a **defeq-plumbing / duplicated-twin file**, not a
duplication-of-mathematics file. Its length is driven by (i) `Subtype.val ⁻¹'` / `Subtype.val ''`
transport between the `Spa`, `Spv`, and `↥Y` presentations of the same set, and (ii) the
`windowU`/`windowV` twin structure. Both are mechanically fixable with helper lemmas; the only
mathematically dense proof is `mem_rationalOpen_pair_iff`, which should be left alone (and is a
plausible candidate for promotion to the general `Spa` API, since it mentions `Ainf` only
incidentally).
