# Inventory: PadicLFunctions/Measure/UnitsZp.lean

File-level context: measures on `ℤ_p^×`. Defines the space `Λ(ℤ_p^×) = ℳ(ℤ_p^×, ℤ_p)`, the embedding `ι : Λ(ℤ_p^×) ↪ Λ(ℤ_p)`, and identifies its image with `ker ψ` (RJW arXiv:2309.15692, Rem. 3.33). Topology on `ℤ_[p]ˣ` is the standard units topology; `Units.val` is a closed embedding with clopen range `{x | IsUnit x} = {x | ‖x‖ = 1}`.

File-level: `variable (p : ℕ) [hp : Fact p.Prime]`; `noncomputable section`; `namespace PadicMeasure`; `open scoped fwdDiff`.

---

### lemma isClosed_range_embedProduct
- Type: `IsClosed (Set.range (Units.embedProduct ℤ_[p]))`
- What: The range of the embedding `ℤ_[p]ˣ → ℤ_[p] × ℤ_[p]ᵐᵒᵖ` (via `embedProduct`) is a closed subset of the product space.
- How: Rewrites the range as the intersection of two closed sets `{q | q.1 * q.2.unop = 1}` and `{q | q.2.unop * q.1 = 1}` (each cut out by `isClosed_eq` of two continuous maps); the set-equality is proved by `ext` + `constructor`, building a unit from the two-sided inverse via the `Units.mk` constructor `⟨q.1, q.2.unop, h1, h2⟩`.
- Hypotheses: `p` prime (ambient `Fact p.Prime`).
- Uses from project: []
- Used by: `instance CompactSpace ℤ_[p]ˣ`
- Visibility: private
- Lines: 24–41 (proof ~17 lines)
- Notes: none

### instance (CompactSpace ℤ_[p]ˣ)
- Type: `CompactSpace ℤ_[p]ˣ`
- What: `ℤ_[p]ˣ` is compact, since it embeds as a closed subset of the compact product `ℤ_[p] × ℤ_[p]ᵐᵒᵖ`. Noted as not in mathlib (verified absent).
- How: Uses `Units.isEmbedding_embedProduct.isCompact_iff` to reduce to compactness of the image of `univ`, then `Set.image_univ` turns it into the range, which is closed (`isClosed_range_embedProduct`) hence compact via `.isCompact`.
- Hypotheses: `p` prime.
- Uses from project: [`isClosed_range_embedProduct`]
- Used by: unused in file (instance; relied on implicitly by later T2/compact-to-T2 homeomorphism arguments)
- Visibility: public (instance)
- Lines: 43–48 (proof ~3 lines)
- Notes: none

### instance (TotallyDisconnectedSpace ℤ_[p]ᵐᵒᵖ)
- Type: `TotallyDisconnectedSpace ℤ_[p]ᵐᵒᵖ`
- What: The multiplicative opposite `ℤ_[p]ᵐᵒᵖ` is totally disconnected.
- How: Transports total disconnectedness of `ℤ_[p]` through the homeomorphism `MulOpposite.opHomeomorph.symm`, using that an embedding's range is totally disconnected (`isTotallyDisconnected_range`) and `isTotallyDisconnected_of_totallyDisconnectedSpace`.
- Hypotheses: `p` prime.
- Uses from project: []
- Used by: unused in file (instance; supports `TotallyDisconnectedSpace ℤ_[p]ˣ`)
- Visibility: public (instance)
- Lines: 50–52 (proof ~2 lines)
- Notes: none

### instance (TotallyDisconnectedSpace ℤ_[p]ˣ)
- Type: `TotallyDisconnectedSpace ℤ_[p]ˣ`
- What: `ℤ_[p]ˣ` is totally disconnected, inherited through its embedding into `ℤ_[p] × ℤ_[p]ᵐᵒᵖ`.
- How: Same pattern as the opposite case — `Units.isEmbedding_embedProduct.isTotallyDisconnected_range.1` applied to `isTotallyDisconnected_of_totallyDisconnectedSpace` of the product.
- Hypotheses: `p` prime.
- Uses from project: []
- Used by: unused in file (instance)
- Visibility: public (instance)
- Lines: 54–57 (proof ~2 lines)
- Notes: none

### def unitsValCM
- Type: `C(ℤ_[p]ˣ, ℤ_[p])`
- What: The coercion `ℤ_[p]ˣ → ℤ_[p]`, `u ↦ (u : ℤ_[p])`, packaged as a continuous map (bundled `ContinuousMap`).
- How: Bundles `fun u => (u : ℤ_[p])` with continuity witness `Units.continuous_val`.
- Hypotheses: `p` prime.
- Uses from project: []
- Used by: `iota`, `extendByZero_comp_val`, `res_iota`, `extendByZero_comp_unitsVal`, `mem_range_iota_iff` (and indirectly all `iota`-consumers)
- Visibility: public
- Lines: 59–61 (definition, no proof body)
- Notes: none

### def unitsHomeo
- Type: `ℤ_[p]ˣ ≃ₜ {x : ℤ_[p] | IsUnit x}`
- What: A homeomorphism between `ℤ_[p]ˣ` and the clopen subset of units of `ℤ_[p]`.
- How: Builds the equivalence `u ↦ ⟨(u:ℤ_[p]), u.isUnit⟩` with inverse `y ↦ y.2.unit` (left/right inverses via `Units.ext` / `Subtype.ext` and `IsUnit.unit_spec`), then upgrades to a homeomorphism using `Continuous.homeoOfEquivCompactToT2` (continuous bijection from compact `ℤ_[p]ˣ` to Hausdorff target), with continuity from `Units.continuous_val.subtype_mk`.
- Hypotheses: `p` prime; uses compactness of `ℤ_[p]ˣ` and Hausdorffness of the target.
- Uses from project: [] (relies on the `CompactSpace ℤ_[p]ˣ` instance above, but no named project decl)
- Used by: `extendByZero` (via `.symm`)
- Visibility: public (noncomputable)
- Lines: 63–71 (definition, ~6 lines of equiv data)
- Notes: none

### def extendByZero
- Type: `C(ℤ_[p]ˣ, ℤ_[p]) →ₗ[ℤ_[p]] C(ℤ_[p], ℤ_[p])`
- What: Extension-by-zero linear map: sends a continuous function `g` on the units to the continuous function on `ℤ_[p]` equal to `g` on units and `0` elsewhere; auxiliary for surjectivity of restriction and injectivity of `ι`.
- How: `toFun g` is `fun x => if h : IsUnit x then g h.unit else 0`; continuity is shown pointwise via `continuous_iff_continuousAt`, splitting on `IsUnit x`: on the clopen units it equals `g ∘ (unitsHomeo p).symm` (continuous), off the units it is locally constant `0` (`ContinuousOn.congr` with `continuousOn_const`), using `isClopen_units` to get neighborhoods. Linearity (`map_add'`, `map_smul'`) by `ext` + `by_cases IsUnit x` + `simp`.
- Hypotheses: `p` prime; `open Classical` (for the decidable `if h : IsUnit x`).
- Uses from project: [`isClopen_units`, `unitsHomeo`]
- Used by: `extendByZero_coe_unit`, `extendByZero_comp_val`, `extendByZero_comp_unitsVal`, `mem_range_iota_iff`
- Visibility: public (noncomputable)
- Lines: 73–106 (proof/body ~31 lines, mostly the continuity obligation)
- Notes: long(30-50); `open Classical in`

### lemma extendByZero_coe_unit
- Type: `extendByZero p g (u : ℤ_[p]) = g u` for `g : C(ℤ_[p]ˣ, ℤ_[p])`, `u : ℤ_[p]ˣ`
- What: Evaluating the zero-extension at the image `(u : ℤ_[p])` of a unit returns the original value `g u`.
- How: Reduces to the `dif_pos` branch using `hx : IsUnit (u:ℤ_[p])` from `u.isUnit`, then `congrArg g` with `Units.ext (IsUnit.unit_spec hx)` to identify `hx.unit` with `u`.
- Hypotheses: `p` prime; `open Classical`.
- Uses from project: [`extendByZero`]
- Used by: `extendByZero_comp_val`
- Visibility: public; `@[simp]`
- Lines: 108–115 (proof ~5 lines)
- Notes: none; `@[simp]`, `open Classical in`

### def iota
- Type: `PadicMeasure p ℤ_[p]ˣ →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p]`
- What: The embedding `ι : Λ(ℤ_p^×) → Λ(ℤ_p)` defined by pushforward along `unitsValCM`, so `∫_{ℤ_p} φ d(ιμ) = ∫_{ℤ_p^×} φ|_{ℤ_p^×} dμ` (RJW Rem. 3.33).
- How: Defined directly as `pushforward p (unitsValCM p)`.
- Hypotheses: `p` prime.
- Uses from project: [`pushforward`, `unitsValCM`]
- Used by: `iota_injective`, `res_iota`, `mem_range_iota_iff`
- Visibility: public (noncomputable)
- Lines: 117–122 (definition, no proof)
- Notes: none

### lemma extendByZero_comp_val
- Type: `(extendByZero p g).comp (unitsValCM p) = g` for `g : C(ℤ_[p]ˣ, ℤ_[p])`
- What: Restricting the zero-extension back to the units (composing with `unitsValCM`) recovers the original function `g`.
- How: `ContinuousMap.ext` reducing to the pointwise identity `extendByZero_coe_unit`.
- Hypotheses: `p` prime.
- Uses from project: [`extendByZero`, `unitsValCM`, `extendByZero_coe_unit`]
- Used by: `iota_injective`
- Visibility: public
- Lines: 124–127 (proof ~2 lines)
- Notes: none

### theorem iota_injective
- Type: `Function.Injective (iota p)`
- What: `ι` is injective; equivalently, the restriction map `C(ℤ_p, ℤ_p) → C(ℤ_p^×, ℤ_p)` is surjective (witnessed by extension by zero). RJW Rem. 3.33 ("we can identify `Λ(ℤ_p^×)` with its image").
- How: Given `iota p μ = iota p ν`, proves `μ = ν` via `LinearMap.ext fun g`; rewrites with `iota`/`pushforward_apply`/`extendByZero_comp_val` so that `μ g = μ ((extendByZero p g).comp (unitsValCM p))`, then applies `LinearMap.congr_fun h (extendByZero p g)`.
- Hypotheses: `p` prime.
- Uses from project: [`iota`, `pushforward` (via `pushforward_apply`), `extendByZero`, `extendByZero_comp_val`]
- Used by: unused in file
- Visibility: public (theorem)
- Lines: 129–136 (proof ~4 lines)
- Notes: none

### theorem res_iota
- Type: `res p (isClopen_units p) (iota p μ) = iota p μ` for `μ : PadicMeasure p ℤ_[p]ˣ`
- What: `Res_{ℤ_p^×} ∘ ι = ι`; the image of `ι` consists of measures supported on the units. RJW Rem. 3.33.
- How: `LinearMap.ext fun f`; via `change` reduces to `μ ((charFn(units) * f).comp (unitsValCM)) = μ (f.comp (unitsValCM))`, then `congr 1` + `ext u` and `simp` using `Set.indicator_of_mem` (since `(u:ℤ_[p]) ∈ {x | IsUnit x}`) collapsing the indicator factor to `1`.
- Hypotheses: `p` prime; `isClopen_units p` (units form a clopen set).
- Uses from project: [`res`, `isClopen_units`, `iota`, `unitsValCM`]
- Used by: `mem_range_iota_iff`
- Visibility: public (theorem)
- Lines: 138–151 (proof ~10 lines)
- Notes: none

### lemma extendByZero_comp_unitsVal
- Type: `extendByZero p (f.comp (unitsValCM p)) = (charFn ℤ_[p] (isClopen_units p)) * f` for `f : C(ℤ_[p], ℤ_[p])`
- What: Zero-extending the restriction of `f` to the units equals multiplying `f` by the indicator (characteristic function) of the units.
- How: `ext x`, `change` to the `dif` form, then `by_cases IsUnit x`: on units `simp` with `Set.indicator_of_mem`, `IsUnit.unit_spec` (so `(f.comp unitsValCM) hx.unit = f x`) giving `1 * f x`; off units `simp` with `Set.indicator_of_notMem` giving `0 * f x = 0`.
- Hypotheses: `p` prime; `open Classical`; `isClopen_units p`.
- Uses from project: [`extendByZero`, `unitsValCM`, `isClopen_units`]
- Used by: `mem_range_iota_iff`
- Visibility: public
- Lines: 153–167 (proof ~12 lines)
- Notes: none; `open Classical in`

### theorem mem_range_iota_iff
- Type: `μ ∈ Set.range (iota p) ↔ psi p μ = 0` for `μ : PadicMeasure p ℤ_[p]`
- What: The image of `ι` is exactly `ker ψ`: a measure `μ ∈ Λ(ℤ_p)` lies in `Λ(ℤ_p^×)` iff `ψ(μ) = 0`. RJW Rem. 3.33 / Cor. 3.32.
- How: Two directions. (⇒) Given `μ = iota p ν`, rewrite via `← isSupportedOn_units_iff_psi_eq_zero` and discharge with `res_iota`. (⇐) Given `psi p μ = 0`, exhibit the preimage `μ.comp (extendByZero p)`; via `LinearMap.ext` + `change` + `extendByZero_comp_unitsVal`, reduce to `μ (charFn(units) * f) = μ f`, closed by `LinearMap.congr_fun` of `(isSupportedOn_units_iff_psi_eq_zero p μ).2 h`.
- Hypotheses: `p` prime.
- Uses from project: [`iota`, `psi`, `isSupportedOn_units_iff_psi_eq_zero`, `res_iota`, `extendByZero`, `unitsValCM`, `extendByZero_comp_unitsVal`]
- Used by: unused in file
- Visibility: public (theorem)
- Lines: 169–184 (proof ~10 lines)
- Notes: none

---

## File Summary

- Total declarations: 13 — defs: 4 (`unitsValCM`, `unitsHomeo`, `extendByZero`, `iota`); lemmas+theorems: 6 (`isClosed_range_embedProduct`, `extendByZero_coe_unit`, `extendByZero_comp_val`, `iota_injective`, `res_iota`, `extendByZero_comp_unitsVal`, `mem_range_iota_iff` — 7 named results, of which `iota_injective`/`res_iota`/`mem_range_iota_iff` are `theorem`); instances: 3 (`CompactSpace ℤ_[p]ˣ`, `TotallyDisconnectedSpace ℤ_[p]ᵐᵒᵖ`, `TotallyDisconnectedSpace ℤ_[p]ˣ`). [Counts: 4 defs + 7 lemmas/theorems + 3 instances = 14 entries incl. the private lemma; 13 distinct exported decls + 1 private.]
- Key API (used by ≥3 decls in-file): `unitsValCM` (used by 5+), `extendByZero` (used by 4), `iota` (used by 3). `isClopen_units` (project import) used by 4.
- Unused in file (no downstream consumer within this file): `CompactSpace ℤ_[p]ˣ`, both `TotallyDisconnectedSpace` instances, `iota_injective`, `mem_range_iota_iff` (terminal API exported for other modules).
- Decls with `sorry`: none.
- `set_option`: none. `open Classical in` used on 4 decls (`extendByZero`, `extendByZero_coe_unit`, `extendByZero_comp_unitsVal`, and the `mem_range_iota_iff` block does not). TODO/admit: none.
- Proofs > 50 lines (OVER-50): none (count 0).
- Proofs 30–50 lines (long): 1 — `extendByZero` (~31 lines, the continuity obligation). Count: 1.
