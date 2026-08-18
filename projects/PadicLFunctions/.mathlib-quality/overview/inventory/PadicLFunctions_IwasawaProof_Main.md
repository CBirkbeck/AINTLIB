# Inventory: PadicLFunctions/IwasawaProof/Main.lean

File namespace: `PadicLFunctions.Coleman`. Universal section variables: `(p : ℕ) [hp : Fact p.Prime]`. Whole file is `noncomputable section`.

Milestone file (RJW §12.5, "Iwasawa's theorem", `thm:iwasawa 2`): the Coleman map `Col` descends to (i) a SES `0 → 𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p → ℤ_p(1) → 0` and (ii) the iso `𝒰⁺_{∞,1}/𝒞⁺_{∞,1} ≅ Λ(𝒢⁺)/I(𝒢⁺)ζ_p`.

---

### theorem Col_one
- Type: `Col p (1 : NormCompatUnits p) = 0`
- What: The Coleman map sends the trivial norm-compatible unit system (all levels `= 1`) to the zero measure.
- How: Direct application — the trivial system is `(p−1)`-torsion (each level satisfies `1 = 1^k`), so `Col_eq_zero_of_torsion` kills it.
- Hypotheses: none beyond the global `p` prime.
- Uses from project: [`Col`, `Col_eq_zero_of_torsion`, `NormCompatUnits`]
- Used by: `ColMul`, `colImageSubgroup`, `zetaIdeal_le_col_image` (transitively via subgroup proofs), `Col_galNCU_wGamma_inv`, `colPreimageZeta`, `ColPlusMul`, `mem_cycloTower1_of_col_mem_zetaIdeal`, `col_mem_zetaIdeal_of_mem_cycloTower1`
- Visibility: public
- Lines: 56–57 (proof 1 line)
- Notes: none

### def ColMul
- Type: `(hp2 : p ≠ 2) : NormCompatUnits p →* Multiplicative (PadicMeasure p ℤ_[p]ˣ ⧸ PadicMeasure.zetaIdeal p hp2)`
- What: The Coleman map packaged multiplicatively as a monoid hom `u ↦ [Col u]` into the additive group `Λ(𝒢)/I(𝒢)ζ_p` viewed multiplicatively; the source of the descent.
- How: `toFun` is `ofAdd ∘ (quotient mk) ∘ Col`; `map_one'` from `Col_one` + `map_zero`; `map_mul'` from `Col_add` (turns products into sums) + `map_add` + `ofAdd_add`.
- Hypotheses: `p ≠ 2` (needed for `zetaIdeal` to be defined).
- Uses from project: [`Col`, `Col_one`, `Col_add`, `NormCompatUnits`, `PadicMeasure`, `PadicMeasure.zetaIdeal`]
- Used by: `ColMul_apply`, `colDescentMul`
- Visibility: public
- Lines: 63–70 (proof ~5 lines)
- Notes: none

### theorem ColMul_apply
- Type: `(hp2 : p ≠ 2) (u : NormCompatUnits p) : ColMul p hp2 u = Multiplicative.ofAdd (Ideal.Quotient.mk (PadicMeasure.zetaIdeal p hp2) (Col p u))`
- What: Unfolds the value of `ColMul` to `ofAdd [Col u]` (a `@[simp]` defeq lemma).
- How: `rfl`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`ColMul`, `Col`, `NormCompatUnits`, `PadicMeasure.zetaIdeal`]
- Used by: `colDescentMul`
- Visibility: public (`@[simp]`)
- Lines: 72–75 (proof 1 line / rfl)
- Notes: none

### theorem Col_cyclo_mem_zetaIdeal
- Type: `(hp2 : p ≠ 2) : Col p (cyclo p (…).choose_spec.choose_spec.1 hp2) ∈ PadicMeasure.zetaIdeal p hp2`
- What: The canonical cyclotomic generator `c(a₀)` has `Col(c(a₀)) = −zetaNum a₀`, which lies in the ζ-ideal — the bounded (single-generator) facet of the image computation.
- How: Rewrite `Col_cyclo`, then `neg_mem`; membership via `mem_zetaIdeal_iff` with witness `dirac a₀ − 1` in the augmentation ideal (`deg = 1`, `sub_self`) and `IsLocalization.mk'_spec'` giving `([a₀]−1)·ζ_p = zetaNum a₀`.
- Hypotheses: `p ≠ 2`; `a₀` is the integer topological generator from `exists_nat_topological_generator`.
- Uses from project: [`Col`, `cyclo`, `PadicMeasure.zetaIdeal`, `Col_cyclo`, `PadicMeasure.mem_zetaIdeal_iff`, `PadicMeasure.dirac`, `PadicMeasure.exists_nat_topological_generator`, `PadicMeasure.augmentationIdeal`, `PadicMeasure.deg`, `PadicMeasure.QuotientField`]
- Used by: unused in file
- Visibility: public
- Lines: 83–95 (proof ~10 lines)
- Notes: none

### theorem ZpOne_le_cycloTower1
- Type: `ZpOne p ≤ cycloTower1 p`
- What: The Tate-twist tower `ℤ_p(1)` (Galois module of `p`-power roots of unity) sits inside the cyclotomic tower `𝒞_{∞,1}`; this places `ker Col` inside `𝒞_{∞,1}`.
- How: Pointwise: take `u ∈ ZpOne`, obtain the exponent `a`; at each level `n ≥ 1`, `ξ_n^a = zpPow ξ_n a` is a `ℤ_p`-limit of integral powers, landing in the closure `𝒞_{n,1}` by `zpPow_zetaSys_mem_cycloClosureOne`.
- Hypotheses: none beyond global.
- Uses from project: [`ZpOne`, `cycloTower1`, `zpPow_zetaSys_mem_cycloClosureOne`]
- Used by: `mem_cycloTower1_of_col_mem_zetaIdeal`
- Visibility: public
- Lines: 103–106 (proof ~4 lines)
- Notes: none

### theorem galNCU_wGamma_inv_mem_cycloTower1
- Type: `(a : ℤ_[p]ˣ) (hp2 : p ≠ 2) : galNCU p a (wGamma p hp2)⁻¹ ∈ cycloTower1 p`
- What: The `𝒢`-translate `σ_a` of the inverse cyclotomic generator `wγ(a₀)⁻¹` stays in the cyclotomic tower.
- How: Rewrite `galNCU_inv` (σ_a commutes with inverse), then `cycloTower1.inv_mem` applied to `galNCU_wGamma_mem_cycloTower1`.
- Hypotheses: `a ∈ ℤ_p^×`, `p ≠ 2`.
- Uses from project: [`galNCU`, `wGamma`, `cycloTower1`, `galNCU_inv`, `galNCU_wGamma_mem_cycloTower1`]
- Used by: `dirac_mul_zetaNum_mem_col_image`
- Visibility: public
- Lines: 121–124 (proof ~2 lines)
- Notes: none

### theorem Col_galNCU_wGamma_inv
- Type: `(a : ℤ_[p]ˣ) (hp2 : p ≠ 2) : Col p (galNCU p a (wGamma p hp2)⁻¹) = (PadicMeasure.dirac p a) * PadicMeasure.zetaNum p (…).choose`
- What: The group-element image identity `Col(σ_a · wγ(a₀)⁻¹) = [a]·zetaNum a₀`; as `a` ranges, the RHS ranges over the group-element multiples of `zetaNum a₀`.
- How: First `Col(wγ⁻¹) = −Col(wγ) = zetaNum a₀` from `Col_add` (with `mul_inv_cancel`, `Col_one`) and `Col_wGamma_choose` + `neg_neg`; then `Col_galNCU_eq_dirac_mul` gives `Col(σ_a u) = [a]·Col u`.
- Hypotheses: `a ∈ ℤ_p^×`, `p ≠ 2`.
- Uses from project: [`Col`, `galNCU`, `wGamma`, `PadicMeasure.dirac`, `PadicMeasure.zetaNum`, `PadicMeasure.exists_nat_topological_generator`, `Col_add`, `Col_one`, `Col_wGamma_choose`, `Col_galNCU_eq_dirac_mul`]
- Used by: `dirac_mul_zetaNum_mem_col_image`
- Visibility: public
- Lines: 130–141 (proof ~8 lines)
- Notes: none

### theorem dirac_mul_zetaNum_mem_col_image
- Type: `(a : ℤ_[p]ˣ) (hp2 : p ≠ 2) : (PadicMeasure.dirac p a) * PadicMeasure.zetaNum p (…).choose ∈ Col p '' (cycloTower1 p : Set (NormCompatUnits p))`
- What: Every group-element scalar multiple `[a]·zetaNum a₀` lies in the Coleman image of the cyclotomic tower — the dense facet of the image identity.
- How: Direct witness: the tower element `σ_a(wγ(a₀)⁻¹)` is in `𝒞_{∞,1}` (`galNCU_wGamma_inv_mem_cycloTower1`) and has the right image (`Col_galNCU_wGamma_inv`).
- Hypotheses: `a ∈ ℤ_p^×`, `p ≠ 2`.
- Uses from project: [`PadicMeasure.dirac`, `PadicMeasure.zetaNum`, `PadicMeasure.exists_nat_topological_generator`, `Col`, `cycloTower1`, `NormCompatUnits`, `galNCU`, `wGamma`, `galNCU_wGamma_inv_mem_cycloTower1`, `Col_galNCU_wGamma_inv`]
- Used by: `zetaIdeal_le_col_image`
- Visibility: public
- Lines: 147–152 (proof ~2 lines / term)
- Notes: none

### def colImageSubgroup
- Type: `: AddSubgroup (PadicMeasure p ℤ_[p]ˣ)` with carrier `Col p '' (cycloTower1 p : Set (NormCompatUnits p))`
- What: The image `Col '' 𝒞_{∞,1}` packaged as an additive subgroup of `Λ(ℤ_p^×)` (closed in weak-* topology).
- How: `add_mem'` from `Col_add` on `u*v`; `zero_mem'` from `Col_one` on `1`; `neg_mem'` from `Col_add` on `u*u⁻¹` (with `mul_inv_cancel`, `Col_one`, `eq_neg_of_add_eq_zero_right`).
- Hypotheses: none beyond global.
- Uses from project: [`PadicMeasure`, `Col`, `cycloTower1`, `NormCompatUnits`, `Col_add`, `Col_one`]
- Used by: `zetaIdeal_le_col_image`
- Visibility: public
- Lines: 228–239 (proof ~10 lines)
- Notes: none

### theorem zetaIdeal_le_col_image
- Type: `(hp2 : p ≠ 2) : (PadicMeasure.zetaIdeal p hp2 : Set (PadicMeasure p ℤ_[p]ˣ)) ⊆ Col p '' (cycloTower1 p : Set (NormCompatUnits p))`
- What: The `⊇` half of the image identity — the entire principal ζ-ideal `I(𝒢)ζ_p = (zetaNum a₀)` lands in the Coleman image (the genuine §13/IMC density-crossing, PROVED).
- How: `colImageSubgroup` is closed (`isClosed_col_image`) and contains each `[a]·zetaNum a₀` (`dirac_mul_zetaNum_mem_col_image`); rewrite `zetaIdeal_eq_span` (needs generator hypotheses `hb_gen` from `exists_nat_topological_generator` and `hνeq` from `IsLocalization.mk'_spec'`); reduce to `span{ν} ⊆ H` and close `r·ζ_num a₀ ∈ H` by `mul_mem_of_dirac_mul_mem` (crossing the dense Dirac span by continuity of `s ↦ s·ζ_num a₀`).
- Hypotheses: `p ≠ 2`.
- Uses from project: [`PadicMeasure.zetaIdeal`, `PadicMeasure`, `Col`, `cycloTower1`, `NormCompatUnits`, `colImageSubgroup`, `isClosed_col_image`, `dirac_mul_zetaNum_mem_col_image`, `PadicMeasure.unitsToZModPow`, `PadicMeasure.exists_nat_topological_generator`, `PadicMeasure.QuotientField`, `PadicMeasure.dirac`, `PadicMeasure.padicZeta`, `PadicMeasure.zetaNum`, `PadicMeasure.zetaIdeal_eq_span`, `PadicMeasure.mul_mem_of_dirac_mul_mem`]
- Used by: `mem_cycloTower1_of_col_mem_zetaIdeal`, `col_image_cycloTower1_eq_zetaIdeal`
- Visibility: public
- Lines: 248–276 (proof ~27 lines)
- Notes: none (proof 27 lines, under 30)

### def cycloGenSubgroup
- Type: `(hp2 : p ≠ 2) : Subgroup (NormCompatUnits p)` `:= Subgroup.closure {u | ∃ a : ℤ_[p]ˣ, u = galNCU p a (wGamma p hp2)}`
- What: The cyclic-module generating subgroup `M = ⟨σ_a · wγ(a₀)⟩` of `𝒰_∞`; its closure is RJW's cyclic `Λ(𝒢)`-module `𝒞_{∞,1}`.
- How: Definition (subgroup generated by the `𝒢`-translates of `wγ(a₀)`).
- Hypotheses: `p ≠ 2`.
- Uses from project: [`NormCompatUnits`, `galNCU`, `wGamma`]
- Used by: `colPreimageZeta`(no), `cycloGenSubgroup_le_colPreimageZeta`, `closure_cycloGenSubgroup_le_cycloTower1`, `col_image_cycloTower1_le_zetaIdeal_of_density`, `map_elemsMonoidHom_cycloGenSubgroup`, `col_mem_zetaIdeal_of_mem_cycloTower1Plus`
- Visibility: public
- Lines: 299–300 (def, 1 line body)
- Notes: none

### def colPreimageZeta
- Type: `(hp2 : p ≠ 2) : Subgroup (NormCompatUnits p)` with carrier `{u | Col p u ∈ PadicMeasure.zetaIdeal p hp2}`
- What: `Col⁻¹(I(𝒢)ζ_p)` — the units whose Coleman image lands in the ζ-ideal — as a (closed) subgroup of `𝒰_∞`.
- How: `mul_mem'` from `Col_add` + ideal `add_mem`; `one_mem'` from `Col_one` + ideal `zero_mem`; `inv_mem'` from `Col_add` on `u*u⁻¹` + ideal `neg_mem`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`NormCompatUnits`, `Col`, `PadicMeasure.zetaIdeal`, `Col_add`, `Col_one`]
- Used by: `isClosed_colPreimageZeta`, `galNCU_wGamma_mem_colPreimageZeta`, `cycloGenSubgroup_le_colPreimageZeta`, `col_image_cycloTower1_le_zetaIdeal_of_density`
- Visibility: public
- Lines: 306–318 (proof ~10 lines)
- Notes: none

### theorem isClosed_colPreimageZeta
- Type: `(hp2 : p ≠ 2) : IsClosed (colPreimageZeta p hp2 : Set (NormCompatUnits p))`
- What: The preimage `Col⁻¹(I(𝒢)ζ_p)` is closed in the inverse-limit topology on `NormCompatUnits`.
- How: `continuous_Col` pulls back the weak-* closed `isClosed_zetaIdeal` (`IsClosed.preimage`).
- Hypotheses: `p ≠ 2`.
- Uses from project: [`colPreimageZeta`, `NormCompatUnits`, `PadicMeasure.isClosed_zetaIdeal`, `continuous_Col`]
- Used by: `col_image_cycloTower1_le_zetaIdeal_of_density`
- Visibility: public
- Lines: 322–324 (proof 1 line / term)
- Notes: none

### theorem zetaNum_choose_mem_zetaIdeal
- Type: `(hp2 : p ≠ 2) : PadicMeasure.zetaNum p (…).choose ∈ PadicMeasure.zetaIdeal p hp2`
- What: The principal generator `zetaNum a₀ = ([a₀]−1)·ζ_p` lies in the ζ-ideal.
- How: `mem_zetaIdeal_iff` with witness `dirac a₀ − 1` in augmentation ideal (`deg = 1`, `sub_self`) and `IsLocalization.mk'_spec'`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`PadicMeasure.zetaNum`, `PadicMeasure.exists_nat_topological_generator`, `PadicMeasure.zetaIdeal`, `PadicMeasure.mem_zetaIdeal_iff`, `PadicMeasure.dirac`, `PadicMeasure.augmentationIdeal`, `PadicMeasure.deg`, `PadicMeasure.padicZeta`, `PadicMeasure.QuotientField`]
- Used by: `galNCU_wGamma_mem_colPreimageZeta`
- Visibility: public
- Lines: 328–339 (proof ~9 lines)
- Notes: none

### theorem galNCU_wGamma_mem_colPreimageZeta
- Type: `(a : ℤ_[p]ˣ) (hp2 : p ≠ 2) : galNCU p a (wGamma p hp2) ∈ colPreimageZeta p hp2`
- What: Each cyclic generator `σ_a · wγ(a₀)` lands in `Col⁻¹(I(𝒢)ζ_p)` since `Col(σ_a·wγ) = [a]·(−zetaNum a₀)`.
- How: `change` to membership statement, rewrite `Col_galNCU_eq_dirac_mul` and `Col_wGamma_choose`, then ideal `mul_mem_left` + `neg_mem` of `zetaNum_choose_mem_zetaIdeal`.
- Hypotheses: `a ∈ ℤ_p^×`, `p ≠ 2`.
- Uses from project: [`galNCU`, `wGamma`, `colPreimageZeta`, `Col`, `PadicMeasure.zetaIdeal`, `Col_galNCU_eq_dirac_mul`, `Col_wGamma_choose`, `zetaNum_choose_mem_zetaIdeal`]
- Used by: `cycloGenSubgroup_le_colPreimageZeta`, `col_mem_zetaIdeal_of_mem_cycloTower1Plus`
- Visibility: public
- Lines: 344–349 (proof ~4 lines)
- Notes: none

### theorem cycloGenSubgroup_le_colPreimageZeta
- Type: `(hp2 : p ≠ 2) : cycloGenSubgroup p hp2 ≤ colPreimageZeta p hp2`
- What: Well-definedness `Col '' M ⊆ I(𝒢)ζ_p` — the whole generating subgroup `M` lands in the ζ-ideal preimage.
- How: `Subgroup.closure_le`, reduce to generators, apply `galNCU_wGamma_mem_colPreimageZeta`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`cycloGenSubgroup`, `colPreimageZeta`, `galNCU_wGamma_mem_colPreimageZeta`]
- Used by: `col_image_cycloTower1_le_zetaIdeal_of_density`, `col_mem_zetaIdeal_of_mem_cycloTower1Plus`
- Visibility: public
- Lines: 354–358 (proof ~3 lines)
- Notes: none

### theorem closure_cycloGenSubgroup_le_cycloTower1
- Type: `(hp2 : p ≠ 2) : closure (cycloGenSubgroup p hp2 : Set (NormCompatUnits p)) ⊆ (cycloTower1 p : Set (NormCompatUnits p))`
- What: The easy half of `closure(M) = 𝒞_{∞,1}`: the topological closure of `M` sits inside the cyclotomic tower.
- How: `𝒞_{∞,1}` is closed (`isClosed_cycloTower1`), so `closure_subset_iff`; reduce to generators via `Subgroup.closure_le`; each generator is in `cycloTower1` by `galNCU_wGamma_mem_cycloTower1`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`cycloGenSubgroup`, `NormCompatUnits`, `cycloTower1`, `isClosed_cycloTower1`, `galNCU_wGamma_mem_cycloTower1`, `galNCU`, `wGamma`]
- Used by: unused in file
- Visibility: public
- Lines: 363–370 (proof ~5 lines)
- Notes: none

### theorem col_image_cycloTower1_le_zetaIdeal_of_density
- Type: `(hp2 : p ≠ 2) (hdense : (cycloTower1 p : Set _) ⊆ closure (cycloGenSubgroup p hp2 : Set _)) : Col p '' (cycloTower1 p : Set _) ⊆ (PadicMeasure.zetaIdeal p hp2 : Set _)`
- What: The `⊆`-direction of the image identity, conditional on the deferred cyclic-module tower density `𝒞_{∞,1} ⊆ closure(M)`.
- How: Given `u ∈ 𝒞_{∞,1}`: `closure(M)` lies in the closed `colPreimageZeta` (contains `M` via `cycloGenSubgroup_le_colPreimageZeta`, closed via `isClosed_colPreimageZeta`, `closure_subset_iff`), so `𝒞_{∞,1} ⊆ closure(M) ⊆ colPreimageZeta` by `hdense`.
- Hypotheses: `p ≠ 2`; the density hypothesis `hdense`.
- Uses from project: [`cycloTower1`, `cycloGenSubgroup`, `NormCompatUnits`, `Col`, `PadicMeasure.zetaIdeal`, `PadicMeasure`, `colPreimageZeta`, `isClosed_colPreimageZeta`, `cycloGenSubgroup_le_colPreimageZeta`]
- Used by: unused in file (superseded — see comment lines 417–419: the `_of_density` route was unsound at the free level-0 coordinate)
- Visibility: public
- Lines: 377–387 (proof ~6 lines)
- Notes: none. (Conditional theorem with explicit `hdense` hypothesis; documented as superseded by the faithful plus/minus `col_mem` route.)

### theorem mem_cycloTower1_of_col_mem_zetaIdeal
- Type: `(hp2 : p ≠ 2) {u : NormCompatUnits p} (hu : u ∈ unitsTower1 p) (hCol : Col p u ∈ PadicMeasure.zetaIdeal p hp2) : u ∈ cycloTower1 p`
- What: The injectivity corollary (`→` direction of the image iff): a principal-unit tower whose Coleman image lies in the ζ-ideal is cyclotomic. Axiom-clean.
- How: The proved `⊇` half `zetaIdeal_le_col_image` gives cyclotomic `c` with `Col c = Col u`; then `Col(u·c⁻¹) = Col u − Col c = 0` (via `Col_add`, `hinv` from `mul_inv_cancel`+`Col_one`); so `u·c⁻¹ ∈ ker Col = ℤ_p(1)` (`mem_ker_Col_iff_mem_ZpOne`) `⊆ 𝒞_{∞,1}` (`ZpOne_le_cycloTower1`); finally `u = (u·c⁻¹)·c ∈ 𝒞_{∞,1}`.
- Hypotheses: `p ≠ 2`; `u ∈ unitsTower1` (principal-unit tower); `Col u ∈ I(𝒢)ζ_p`.
- Uses from project: [`NormCompatUnits`, `unitsTower1`, `Col`, `PadicMeasure.zetaIdeal`, `cycloTower1`, `zetaIdeal_le_col_image`, `Col_add`, `Col_one`, `mem_ker_Col_iff_mem_ZpOne`, `ZpOne_le_cycloTower1`, `cycloTower1_le_unitsTower1`]
- Used by: `col_mem_zetaIdeal_iff_mem_cycloTower1`, `colDescentPlusMul_injective`
- Visibility: public
- Lines: 426–446 (proof ~18 lines)
- Notes: none

### def elemsMonoidHom
- Type: `(n : ℕ) : NormCompatUnits p →* ℂ_[p]ˣ`
- What: The level-`n` coordinate projection as a monoid hom (multiplicative + unital levelwise).
- How: `toFun u := u.elems n`; `map_one'`, `map_mul'` are `rfl`.
- Hypotheses: level index `n`.
- Uses from project: [`NormCompatUnits`]
- Used by: `map_elemsMonoidHom_cycloGenSubgroup`, `col_mem_zetaIdeal_of_mem_cycloTower1Plus`
- Visibility: public
- Lines: 449–452 (proof rfl)
- Notes: none

### theorem map_elemsMonoidHom_cycloGenSubgroup
- Type: `(hp2 : p ≠ 2) (n : ℕ) : Subgroup.map (elemsMonoidHom p n) (cycloGenSubgroup p hp2) = cycloTranslateSubgroup p n ((wGamma p hp2).elems n)`
- What: The level-`n` image of the generating subgroup `M` equals the `𝒢_n`-translate subgroup of `wγ(a₀)`'s level-`n` coordinate.
- How: `Subgroup.map_closure` + `MonoidHom.map_closure`; `congr` then `ext`, with the two set inclusions both witnessed by `galNCU_elems_eq_galAutValU`.
- Hypotheses: `p ≠ 2`, level `n`.
- Uses from project: [`elemsMonoidHom`, `cycloGenSubgroup`, `cycloTranslateSubgroup`, `wGamma`, `galNCU`, `galNCU_elems_eq_galAutValU`]
- Used by: `col_mem_zetaIdeal_of_mem_cycloTower1Plus`
- Visibility: public
- Lines: 457–467 (proof ~9 lines)
- Notes: none

### theorem col_mem_zetaIdeal_of_mem_cycloTower1Plus
- Type: `(hp2 : p ≠ 2) {u : NormCompatUnits p} (hu : u ∈ cycloTower1Plus p) : Col p u ∈ PadicMeasure.zetaIdeal p hp2`
- What: (T1223) A plus-cyclotomic tower unit has Coleman image in the ζ-ideal — the plus-part input to the well-definedness half.
- How: `Col u ∈ closure(Col '' M)` by `Col_mem_closure_image_of_levelwise`: at each `n ≥ 1`, `u.elems n ∈ closure(𝒢_n-translate)` (T1222 `cycloClosureOnePlus_le_closure_wGammaTranslate`), and `elems_n '' M = Units.val '' (translate subgroup)` (`map_elemsMonoidHom_cycloGenSubgroup`) modulo continuous `Units.val` (`image_closure_subset_closure_image`). Then `closure_minimal` into the closed `isClosed_zetaIdeal`, with `closure(Col '' M) ⊆ I(𝒢)ζ_p` via `cycloGenSubgroup_le_colPreimageZeta`.
- Hypotheses: `p ≠ 2`; `u ∈ cycloTower1Plus`.
- Uses from project: [`NormCompatUnits`, `cycloTower1Plus`, `Col`, `PadicMeasure.zetaIdeal`, `cycloGenSubgroup`, `Col_mem_closure_image_of_levelwise`, `cycloTranslateSubgroup`, `wGamma`, `cycloClosureOnePlus_le_closure_wGammaTranslate`, `map_elemsMonoidHom_cycloGenSubgroup`, `PadicMeasure.isClosed_zetaIdeal`, `cycloGenSubgroup_le_colPreimageZeta`]
- Used by: `col_mem_zetaIdeal_of_mem_cycloTower1`
- Visibility: public
- Lines: 476–494 (proof ~17 lines)
- Notes: none

### theorem mem_ZpOne_of_mem_cycloTower1_cAnti
- Type: `(hp2 : p ≠ 2) {z : NormCompatUnits p} (hz : z ∈ cycloTower1 p) (hc : galNCU p (-1) z = z⁻¹) : z ∈ ZpOne p`
- What: (T1224') The `c`-anti-invariant part of the cyclotomic closure is the `ξ`-power tower: a cyclotomic-tower unit fixed up to inversion by complex conjugation `σ_{-1}` lies in `ℤ_p(1)`.
- How: NOT PROVED — body is `sorry`.
- Hypotheses: `p ≠ 2`; `z ∈ cycloTower1`; `σ_{-1}(z) = z⁻¹` (`c`-anti-invariance).
- Uses from project: [`NormCompatUnits`, `cycloTower1`, `galNCU`, `ZpOne`]
- Used by: `col_mem_zetaIdeal_of_mem_cycloTower1`
- Visibility: public
- Lines: 500–502 (proof = sorry)
- Notes: **sorry** — open obligation (RJW lem:cyc units gen (ii)).

### theorem col_mem_zetaIdeal_of_mem_cycloTower1
- Type: `(hp2 : p ≠ 2) {u : NormCompatUnits p} (hu' : u ∈ cycloTower1 p) : Col p u ∈ PadicMeasure.zetaIdeal p hp2`
- What: The well-definedness half (`u ∈ 𝒞_{∞,1} ⟹ Col u ∈ I(𝒢)ζ_p`), via the faithful plus/minus split (Route-P).
- How: Split `Col u` into `c`-plus and `c`-minus parts. Plus: `u·σ_{-1}(u) ∈ 𝒞⁺_{∞,1}` (membership reshuffles `cycloClosureOne`/`localUnitsOnePlus`/`cycloClosurePlus` ⊓-factors; fixed by `galNCU_neg_one_involutive`, `galNCU_neg_one_fixed_mem_unitsTower1Plus`) gives `Col(u·σ_{-1}(u)) ∈ I(𝒢)ζ_p` (`col_mem_zetaIdeal_of_mem_cycloTower1Plus`, T1223). Minus: `u·σ_{-1}(u)⁻¹` is `c`-anti-invariant in `𝒞_{∞,1}`, hence in `ℤ_p(1)` (`mem_ZpOne_of_mem_cycloTower1_cAnti`, T1224'), so `Col = 0` (`mem_ker_Col_iff_mem_ZpOne`). Combining gives `[−1]·Col u = Col u` (`hfix`), then `Col(u·σ_{-1}(u)) = 2·Col u ∈ I(𝒢)ζ_p`; `2` a unit (`isUnit_two_padicInt`, `smul_of_tower_mem`) yields `Col u ∈ I(𝒢)ζ_p`.
- Hypotheses: `p ≠ 2`; `u ∈ cycloTower1`.
- Uses from project: [`NormCompatUnits`, `cycloTower1`, `Col`, `PadicMeasure.zetaIdeal`, `galNCU`, `galNCU_neg_one_mem_cycloTower1`, `Col_galNCU_eq_dirac_mul`, `PadicMeasure.dirac`, `galNCU_mul`, `galNCU_neg_one_involutive`, `unitsTower1Plus`, `galNCU_neg_one_fixed_mem_unitsTower1Plus`, `cycloTower1_le_unitsTower1`, `cycloClosureOne`, `localUnitsOnePlus`, `cycloClosureOnePlus`, `cycloClosurePlus`, `cycloTower1Plus`, `col_mem_zetaIdeal_of_mem_cycloTower1Plus`, `galNCU_inv`, `Col_add`, `Col_one`, `mem_ker_Col_iff_mem_ZpOne`, `mem_ZpOne_of_mem_cycloTower1_cAnti`, `PadicLFunctions.isUnit_two_padicInt`, `PadicMeasure.zetaIdeal.smul_of_tower_mem`]
- Used by: `col_image_cycloTower1_eq_zetaIdeal`, `col_mem_zetaIdeal_iff_mem_cycloTower1`, `colDescentMul`, `colDescentPlusMul`
- Visibility: public
- Lines: 512–559 (proof ~47 lines)
- Notes: **long(30-50)** — proof ~47 lines; depends transitively on the `sorry` in `mem_ZpOne_of_mem_cycloTower1_cAnti`.

### theorem col_image_cycloTower1_eq_zetaIdeal
- Type: `(hp2 : p ≠ 2) : (Col p '' (cycloTower1 p : Set (NormCompatUnits p))) = PadicMeasure.zetaIdeal p hp2`
- What: The §12.5 image computation `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p` (RJW thm:iwasawa 2 image identity).
- How: `le_antisymm`: `⊆` is the faithful plus/minus `col_mem_zetaIdeal_of_mem_cycloTower1`; `⊇` is the density-crossing `zetaIdeal_le_col_image`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`Col`, `cycloTower1`, `NormCompatUnits`, `PadicMeasure.zetaIdeal`, `col_mem_zetaIdeal_of_mem_cycloTower1`, `zetaIdeal_le_col_image`]
- Used by: unused in file (referenced in docstrings/comments of milestones, but not in code)
- Visibility: public
- Lines: 564–569 (proof ~5 lines)
- Notes: none in body; transitively rests on the `sorry` in `mem_ZpOne_of_mem_cycloTower1_cAnti`.

### theorem col_mem_zetaIdeal_iff_mem_cycloTower1
- Type: `(hp2 : p ≠ 2) {u : NormCompatUnits p} (hu : u ∈ unitsTower1 p) : Col p u ∈ PadicMeasure.zetaIdeal p hp2 ↔ u ∈ cycloTower1 p`
- What: The full image iff for principal-unit towers: `Col u ∈ I(𝒢)ζ_p` exactly when `u ∈ 𝒞_{∞,1}`.
- How: Both directions packaged: `mem_cycloTower1_of_col_mem_zetaIdeal` and `col_mem_zetaIdeal_of_mem_cycloTower1`.
- Hypotheses: `p ≠ 2`; `u ∈ unitsTower1`.
- Uses from project: [`NormCompatUnits`, `unitsTower1`, `Col`, `PadicMeasure.zetaIdeal`, `cycloTower1`, `mem_cycloTower1_of_col_mem_zetaIdeal`, `col_mem_zetaIdeal_of_mem_cycloTower1`]
- Used by: unused in file (referenced in docstrings of `colDescentMul`/`colDescentPlusMul`/`colDescentPlusMul_injective`, but those call `col_mem_zetaIdeal_of_mem_cycloTower1` directly)
- Visibility: public
- Lines: 571–574 (proof 1 line / term)
- Notes: none

### def colDescentMul
- Type: `(hp2 : p ≠ 2) : (↥(unitsTower1 p) ⧸ (cycloTower1 p).subgroupOf (unitsTower1 p)) →* Multiplicative (PadicMeasure p ℤ_[p]ˣ ⧸ PadicMeasure.zetaIdeal p hp2)`
- What: (RJW thm:iwasawa 2 (i), genuine map) The descent of `Col` to `𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p`, `[u] ↦ [Col u]`, packaged multiplicatively — the SES injection.
- How: `QuotientGroup.lift` of `(ColMul).comp subtype` through `𝒞_{∞,1}`; cyclotomic units land in `ker` because `Col x ∈ I(𝒢)ζ_p` (`col_mem_zetaIdeal_of_mem_cycloTower1`), so `[Col x] = 0` (`Ideal.Quotient.eq_zero_iff_mem`).
- Hypotheses: `p ≠ 2`.
- Uses from project: [`unitsTower1`, `cycloTower1`, `PadicMeasure`, `PadicMeasure.zetaIdeal`, `ColMul`, `ColMul_apply`, `Col`, `NormCompatUnits`, `col_mem_zetaIdeal_of_mem_cycloTower1`]
- Used by: `colDescent`
- Visibility: public
- Lines: 584–595 (proof ~8 lines)
- Notes: none

### def colDescent
- Type: `(hp2 : p ≠ 2) : Additive (↥(unitsTower1 p) ⧸ (cycloTower1 p).subgroupOf (unitsTower1 p)) →+ (PadicMeasure p ℤ_[p]ˣ ⧸ PadicMeasure.zetaIdeal p hp2)`
- What: (RJW thm:iwasawa 2 (i), additive shape) The additive form of the SES injection `𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p`.
- How: `MonoidHom.toAdditive` applied to `colDescentMul`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`unitsTower1`, `cycloTower1`, `PadicMeasure`, `PadicMeasure.zetaIdeal`, `colDescentMul`]
- Used by: `iwasawa_exact_sequence`
- Visibility: public
- Lines: 600–603 (proof 1 line / term)
- Notes: none

### theorem cycloTower1Plus_le_cycloTower1
- Type: `cycloTower1Plus p ≤ cycloTower1 p`
- What: The plus closure-tower `𝒞⁺_{∞,1}` sits inside the full closure-tower `𝒞_{∞,1}` (drops the `localUnitsPlus` factor).
- How: Pointwise/levelwise: unfold `cycloClosureOnePlus`/`cycloClosurePlus` `⊓`-definitions via `Subgroup.mem_inf`, then re-assemble `cycloClosureOne`.
- Hypotheses: none beyond global.
- Uses from project: [`cycloTower1Plus`, `cycloTower1`, `cycloClosureOnePlus`, `cycloClosurePlus`, `cycloClosureOne`]
- Used by: `colDescentPlusMul`
- Visibility: public
- Lines: 609–614 (proof ~5 lines)
- Notes: none

### theorem cycloTower1Plus_le_unitsTower1Plus
- Type: `cycloTower1Plus p ≤ unitsTower1Plus p`
- What: The plus closure-tower is principal-plus: `𝒞⁺_{∞,1} ≤ 𝒰⁺_{∞,1}`.
- How: Levelwise reshuffle of the `⊓`-factors (`cycloClosureOnePlus`, `cycloClosurePlus`, `localUnitsOnePlus` via `Subgroup.mem_inf`).
- Hypotheses: none beyond global.
- Uses from project: [`cycloTower1Plus`, `unitsTower1Plus`, `cycloClosureOnePlus`, `cycloClosurePlus`, `localUnitsOnePlus`]
- Used by: unused in file
- Visibility: public
- Lines: 618–623 (proof ~5 lines)
- Notes: none

### theorem zetaIdealPlus_eq_map_projPlus
- Type: `(hp2 : p ≠ 2) : PadicMeasure.zetaIdealPlus p hp2 = (PadicMeasure.zetaIdeal p hp2).map (PadicMeasure.projPlus p)`
- What: The ζ-ideal commutes with the plus-projection: `I(𝒢⁺)ζ_p = π_*(I(𝒢)ζ_p)` — the bridge carrying the (i) image computation to the plus side.
- How: Both ideals principal at the common witness `zetaNum a₀`: rewrite `zetaIdealPlus_eq_span` and `zetaIdeal_eq_span` (with generator hypotheses `hb_gen`, `hν` via `IsLocalization.mk'_spec'`), then `Ideal.map_span` + `Set.image_singleton`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`PadicMeasure.zetaIdealPlus`, `PadicMeasure.zetaIdeal`, `PadicMeasure.projPlus`, `PadicMeasure.unitsToZModPow`, `PadicMeasure.exists_nat_topological_generator`, `PadicMeasure.QuotientField`, `PadicMeasure.dirac`, `PadicMeasure.padicZeta`, `PadicMeasure.zetaNum`, `PadicMeasure.zetaIdealPlus_eq_span`, `PadicMeasure.zetaIdeal_eq_span`]
- Used by: `projPlus_zetaIdeal_le_zetaIdealPlus`, `mem_zetaIdeal_of_mem_plusPart_projPlus`
- Visibility: public
- Lines: 631–647 (proof ~14 lines)
- Notes: none

### theorem projPlus_zetaIdeal_le_zetaIdealPlus
- Type: `(hp2 : p ≠ 2) {μ : PadicMeasure p ℤ_[p]ˣ} (hμ : μ ∈ PadicMeasure.zetaIdeal p hp2) : PadicMeasure.projPlus p μ ∈ PadicMeasure.zetaIdealPlus p hp2`
- What: The plus-projection of the ζ-ideal lands in the plus ζ-ideal (the direction needed for the plus descent's well-definedness).
- How: Rewrite `zetaIdealPlus_eq_map_projPlus`, then `Ideal.mem_map_of_mem`.
- Hypotheses: `p ≠ 2`; `μ ∈ I(𝒢)ζ_p`.
- Uses from project: [`PadicMeasure`, `PadicMeasure.zetaIdeal`, `PadicMeasure.projPlus`, `PadicMeasure.zetaIdealPlus`, `zetaIdealPlus_eq_map_projPlus`]
- Used by: `colDescentPlusMul`
- Visibility: public
- Lines: 652–656 (proof ~2 lines)
- Notes: none

### def ColPlusMul
- Type: `(hp2 : p ≠ 2) : NormCompatUnits p →* Multiplicative (PadicMeasure p (PadicMeasure.GPlus p) ⧸ PadicMeasure.zetaIdealPlus p hp2)`
- What: The plus Coleman map as a monoid hom `u ↦ [π_*(Col u)]` into `Λ(𝒢⁺)/I(𝒢⁺)ζ_p`; source of the plus descent.
- How: `toFun` is `ofAdd ∘ mk ∘ projPlus ∘ Col`; `map_one'` from `Col_one`+`map_zero`×2; `map_mul'` from `Col_add`+`map_add`×2+`ofAdd_add`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`NormCompatUnits`, `PadicMeasure`, `PadicMeasure.GPlus`, `PadicMeasure.zetaIdealPlus`, `PadicMeasure.projPlus`, `Col`, `Col_one`, `Col_add`]
- Used by: `ColPlusMul_apply`, `colDescentPlusMul`
- Visibility: public
- Lines: 662–674 (proof ~7 lines)
- Notes: none

### theorem ColPlusMul_apply
- Type: `(hp2 : p ≠ 2) (u : NormCompatUnits p) : ColPlusMul p hp2 u = Multiplicative.ofAdd (Ideal.Quotient.mk (PadicMeasure.zetaIdealPlus p hp2) (PadicMeasure.projPlus p (Col p u)))`
- What: Unfolds `ColPlusMul` to `ofAdd [π_*(Col u)]` (`@[simp]` defeq lemma).
- How: `rfl`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`ColPlusMul`, `PadicMeasure.zetaIdealPlus`, `PadicMeasure.projPlus`, `Col`, `NormCompatUnits`]
- Used by: `colDescentPlusMul`, `colDescentPlusMul_injective`
- Visibility: public (`@[simp]`)
- Lines: 676–680 (proof rfl)
- Notes: none

### def colDescentPlusMul
- Type: `(hp2 : p ≠ 2) : (↥(unitsTower1Plus p) ⧸ (cycloTower1Plus p).subgroupOf (unitsTower1Plus p)) →* Multiplicative (PadicMeasure p (PadicMeasure.GPlus p) ⧸ PadicMeasure.zetaIdealPlus p hp2)`
- What: (RJW thm:iwasawa 2 (ii), genuine plus-descent map) The plus-part Coleman descent `[u] ↦ [π_*(Col u)]` on `𝒰⁺_{∞,1}/𝒞⁺_{∞,1}`.
- How: `QuotientGroup.lift` of `(ColPlusMul).comp subtype`; well-defined because `u ∈ 𝒞⁺_{∞,1} ⟹ u ∈ 𝒞_{∞,1}` (`cycloTower1Plus_le_cycloTower1`) ⟹ `Col u ∈ I(𝒢)ζ_p` (`col_mem_zetaIdeal_of_mem_cycloTower1`) ⟹ `π_*(Col u) ∈ I(𝒢⁺)ζ_p` (`projPlus_zetaIdeal_le_zetaIdealPlus`), so `[π_*(Col x)] = 0`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`unitsTower1Plus`, `cycloTower1Plus`, `PadicMeasure`, `PadicMeasure.GPlus`, `PadicMeasure.zetaIdealPlus`, `ColPlusMul`, `ColPlusMul_apply`, `Col`, `NormCompatUnits`, `cycloTower1Plus_le_cycloTower1`, `cycloTower1`, `col_mem_zetaIdeal_of_mem_cycloTower1`, `projPlus_zetaIdeal_le_zetaIdealPlus`]
- Used by: `colDescentPlusMul_injective`, `colDescentPlusMul_bijective`, `iwasawa_theorem`
- Visibility: public
- Lines: 690–704 (proof ~10 lines)
- Notes: none

### theorem galNCU_neg_one_of_mem_unitsTower1Plus
- Type: `(hp2 : p ≠ 2) {u : NormCompatUnits p} (hu : u ∈ unitsTower1Plus p) : galNCU p (-1) u = u`
- What: A plus-tower unit is fixed by complex conjugation `σ_{-1}` on `𝒰_∞`.
- How: `NormCompatUnits.ext` + `funext` + `Units.ext`; rewrite `galNCU_elems_val`; case split on `n`: `n = 0` uses `σ_{-1} = AlgEquiv.refl` on `K_0 = ℚ_p` (`galAut … 0 = refl`, `dif_neg`); `n ≥ 1` uses `mem_localUnitsOnePlus_iff_galAut_fixed` (Galois fixed-field characterisation `K_n⁺ = (K_n)^{⟨σ_{-1}⟩}`).
- Hypotheses: `p ≠ 2`; `u ∈ unitsTower1Plus`.
- Uses from project: [`NormCompatUnits`, `unitsTower1Plus`, `galNCU`, `galNCU_elems_val`, `galAut`, `localUnitsOne`, `mem_localUnitsOnePlus_iff_galAut_fixed`]
- Used by: `Col_mem_plusPart_of_mem_unitsTower1Plus`
- Visibility: public
- Lines: 719–730 (proof ~10 lines)
- Notes: none

### theorem Col_mem_plusPart_of_mem_unitsTower1Plus
- Type: `(hp2 : p ≠ 2) {u : NormCompatUnits p} (hu : u ∈ unitsTower1Plus p) : Col p u ∈ PadicMeasure.plusPart p`
- What: Plus-equivariance of the Coleman map: for a plus-tower unit, `Col u` is `c`-invariant (lies in `Λ(𝒢)⁺`).
- How: `mem_plusPart_iff`, then `σ_{-1}·u = u` (`galNCU_neg_one_of_mem_unitsTower1Plus`) and `Col_galNCU_eq_dirac_mul` give `[−1]·Col u = Col(σ_{-1}·u) = Col u`.
- Hypotheses: `p ≠ 2`; `u ∈ unitsTower1Plus`.
- Uses from project: [`NormCompatUnits`, `unitsTower1Plus`, `Col`, `PadicMeasure.plusPart`, `PadicMeasure.mem_plusPart_iff`, `Col_galNCU_eq_dirac_mul`, `galNCU`, `galNCU_neg_one_of_mem_unitsTower1Plus`]
- Used by: `colDescentPlusMul_injective`
- Visibility: public
- Lines: 736–740 (proof ~3 lines)
- Notes: none

### theorem mem_cycloTower1Plus_of_mem_cycloTower1_unitsTower1Plus
- Type: `{u : NormCompatUnits p} (hc : u ∈ cycloTower1 p) (hp : u ∈ unitsTower1Plus p) : u ∈ cycloTower1Plus p`
- What: `𝒞⁺_{∞,1} = 𝒞_{∞,1} ⊓ 𝒰⁺_{∞,1}` (the `←` inclusion): cyclotomic + principal-plus ⟹ plus-cyclotomic.
- How: Levelwise reshuffle of `⊓`-factors (`cycloClosureOne`, `localUnitsOnePlus`, `cycloClosureOnePlus`, `cycloClosurePlus` via `Subgroup.mem_inf`).
- Hypotheses: `u ∈ cycloTower1` and `u ∈ unitsTower1Plus`.
- Uses from project: [`NormCompatUnits`, `cycloTower1`, `unitsTower1Plus`, `cycloTower1Plus`, `cycloClosureOne`, `localUnitsOnePlus`, `cycloClosureOnePlus`, `cycloClosurePlus`]
- Used by: `colDescentPlusMul_injective`
- Visibility: public
- Lines: 746–754 (proof ~7 lines)
- Notes: none

### def ePlus
- Type: `(hp2 : p ≠ 2) : PadicMeasure p ℤ_[p]ˣ`
- What: The even idempotent `e⁺ = ½([1] + [−1]) ∈ Λ(𝒢)`, the projector onto `Λ(𝒢)⁺`.
- How: Definition — `(2⁻¹) • (1 + dirac(−1))` using `isUnit_two_padicInt`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`PadicMeasure`, `PadicLFunctions.isUnit_two_padicInt`, `PadicMeasure.dirac`]
- Used by: `ePlus_mem_plusPart`, `projPlus_ePlus`, `mem_zetaIdeal_of_mem_plusPart_projPlus`
- Visibility: **private**
- Lines: 757–759 (def, ~2 lines)
- Notes: none

### theorem dirac_neg_one_sq
- Type: `PadicMeasure.dirac p (-1 : ℤ_[p]ˣ) * PadicMeasure.dirac p (-1 : ℤ_[p]ˣ) = 1`
- What: `[−1]·[−1] = 1` in `Λ(𝒢)`.
- How: `units_dirac_mul_dirac` ((-1)·(-1) = 1 via `neg_mul_neg`), then `units_one_def`.
- Hypotheses: none beyond global.
- Uses from project: [`PadicMeasure.dirac`, `PadicMeasure.units_dirac_mul_dirac`, `PadicMeasure.units_one_def`]
- Used by: `ePlus_mem_plusPart`
- Visibility: **private**
- Lines: 762–765 (proof ~2 lines)
- Notes: none

### theorem ePlus_mem_plusPart
- Type: `(hp2 : p ≠ 2) : ePlus p hp2 ∈ PadicMeasure.plusPart p`
- What: `e⁺ ∈ Λ(𝒢)⁺` (`[−1]·e⁺ = e⁺`).
- How: `mem_plusPart_iff`, unfold `ePlus`, `mul_smul_comm`/`mul_add`/`mul_one`, `dirac_neg_one_sq`, `add_comm`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`ePlus`, `PadicMeasure.plusPart`, `PadicMeasure.mem_plusPart_iff`, `dirac_neg_one_sq`]
- Used by: `mem_zetaIdeal_of_mem_plusPart_projPlus`
- Visibility: **private**
- Lines: 768–770 (proof ~2 lines)
- Notes: none

### theorem projPlus_smul
- Type: `(c : ℤ_[p]) (μ : PadicMeasure p ℤ_[p]ˣ) : PadicMeasure.projPlus p (c • μ) = c • PadicMeasure.projPlus p μ`
- What: `π_*` is `ℤ_[p]`-linear in the scalar action.
- How: `LinearMap.map_smul` of `pushforward (quotientMk)`.
- Hypotheses: scalar `c`, measure `μ`.
- Uses from project: [`PadicMeasure`, `PadicMeasure.projPlus`, `PadicMeasure.pushforward`, `PadicMeasure.quotientMk`]
- Used by: `projPlus_ePlus`
- Visibility: **private**
- Lines: 773–775 (proof 1 line / term)
- Notes: none

### theorem projPlus_ePlus
- Type: `(hp2 : p ≠ 2) : PadicMeasure.projPlus p (ePlus p hp2) = 1`
- What: `π_*(e⁺) = 1` — under the quotient `mk(−1) = mk(1)`, so `e⁺ ↦ ½(1+1) = 1`.
- How: Unfold `ePlus`, `projPlus_smul`, `map_add`/`map_one`, `projPlus_dirac`; collapse `mk(−1) = mk(1)` (`QuotientGroup.eq`, `Subgroup.mem_zpowers_iff`); `dirac(mk 1) = 1`; `1+1 = 2•1`, `smul_smul`, `isUnit_two_padicInt.val_inv_mul`, `one_smul`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`PadicMeasure.projPlus`, `ePlus`, `projPlus_smul`, `PadicMeasure.projPlus_dirac`, `PadicMeasure.units_one_def`, `PadicMeasure`, `PadicLFunctions.isUnit_two_padicInt`]
- Used by: `mem_zetaIdeal_of_mem_plusPart_projPlus`
- Visibility: **private**
- Lines: 778–788 (proof ~9 lines)
- Notes: none

### theorem mem_zetaIdeal_of_mem_plusPart_projPlus
- Type: `(hp2 : p ≠ 2) {μ : PadicMeasure p ℤ_[p]ˣ} (hμ : μ ∈ PadicMeasure.plusPart p) (hproj : PadicMeasure.projPlus p μ ∈ PadicMeasure.zetaIdealPlus p hp2) : μ ∈ PadicMeasure.zetaIdeal p hp2`
- What: The plus ζ-ideal pulls back to the ζ-ideal on `c`-invariant measures: `μ ∈ Λ(𝒢)⁺` and `π_*(μ) ∈ I(𝒢⁺)ζ_p` ⟹ `μ ∈ I(𝒢)ζ_p`.
- How: `zetaIdealPlus_eq_map_projPlus` + `Ideal.mem_map_iff_of_surjective` (`projPlus_surjective`) gives `ν ∈ I(𝒢)ζ_p` with `π_*(ν) = π_*(μ)`; replace by plus part `ν' = e⁺·ν` (still in ideal via `Ideal.mul_mem_left`, in `plusPart` via `mul_mem_plusPart`+`ePlus_mem_plusPart`, same pushforward via `projPlus_ePlus`); `π_*` injective on `Λ(𝒢)⁺` (`plusSection_projPlus`) gives `μ = ν' ∈ I(𝒢)ζ_p`.
- Hypotheses: `p ≠ 2`; `μ ∈ plusPart`; `π_*(μ) ∈ zetaIdealPlus`.
- Uses from project: [`PadicMeasure`, `PadicMeasure.plusPart`, `PadicMeasure.projPlus`, `PadicMeasure.zetaIdealPlus`, `PadicMeasure.zetaIdeal`, `zetaIdealPlus_eq_map_projPlus`, `PadicMeasure.projPlus_surjective`, `ePlus`, `ePlus_mem_plusPart`, `PadicMeasure.mul_mem_plusPart`, `projPlus_ePlus`, `PadicMeasure.plusSection`, `PadicMeasure.plusSection_projPlus`]
- Used by: `colDescentPlusMul_injective`
- Visibility: public
- Lines: 796–817 (proof ~21 lines)
- Notes: none

### theorem colDescentPlusMul_injective
- Type: `(hp2 : p ≠ 2) : Function.Injective (colDescentPlusMul p hp2)`
- What: The plus-descent `colDescentPlusMul` is injective (RJW §12.5, the `⟨c⟩`-invariants half, discharged via the Galois fixed-field).
- How: `injective_iff_map_eq_one`, `QuotientGroup.induction_on`. For plus-tower `u` with `[π_*(Col u)] = 0`: extract `π_*(Col u) ∈ I(𝒢⁺)ζ_p` (`ofAdd` injective, `eq_zero_iff_mem`); `Col u ∈ Λ(𝒢)⁺` (`Col_mem_plusPart_of_mem_unitsTower1Plus`); so `Col u ∈ I(𝒢)ζ_p` (`mem_zetaIdeal_of_mem_plusPart_projPlus`); hence `u ∈ 𝒞_{∞,1}` (`mem_cycloTower1_of_col_mem_zetaIdeal`) and being plus `u ∈ 𝒞⁺_{∞,1}` (`mem_cycloTower1Plus_of_mem_cycloTower1_unitsTower1Plus`), i.e. `[u] = 1`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`colDescentPlusMul`, `ColPlusMul_apply`, `Col`, `NormCompatUnits`, `unitsTower1Plus`, `PadicMeasure.projPlus`, `PadicMeasure.zetaIdealPlus`, `PadicMeasure.plusPart`, `PadicMeasure.zetaIdeal`, `Col_mem_plusPart_of_mem_unitsTower1Plus`, `mem_zetaIdeal_of_mem_plusPart_projPlus`, `unitsTower1`, `unitsTower1Plus_le_unitsTower1`, `cycloTower1`, `mem_cycloTower1_of_col_mem_zetaIdeal`, `cycloTower1Plus`, `mem_cycloTower1Plus_of_mem_cycloTower1_unitsTower1Plus`]
- Used by: `colDescentPlusMul_bijective`
- Visibility: public
- Lines: 829–855 (proof ~25 lines)
- Notes: none

### theorem colDescentPlusMul_bijective
- Type: `(hp2 : p ≠ 2) : Function.Bijective (colDescentPlusMul p hp2)`
- What: (RJW thm:iwasawa 2 (ii), milestone) The plus-descent `𝒰⁺_{∞,1}/𝒞⁺_{∞,1} → Λ(𝒢⁺)/I(𝒢⁺)ζ_p` is bijective.
- How: Pair of `colDescentPlusMul_injective` (proved) and surjectivity (**sorry**); surjectivity is documented to reduce to the `⊆` half of `col_image_cycloTower1_eq_zetaIdeal` via the `(−)^{⟨c⟩}`-collapse of the fundamental sequence (i) (`ℤ_p(1)^{⟨c⟩}=0`, `range_Col_eq_ker_chiMoment`).
- Hypotheses: `p ≠ 2`.
- Uses from project: [`colDescentPlusMul`, `colDescentPlusMul_injective`, `zetaIdeal_le_col_image` (named in comment), `col_image_cycloTower1_eq_zetaIdeal` (named in comment)]
- Used by: `iwasawa_theorem`
- Visibility: public
- Lines: 871–883 (proof ~12 lines, surjectivity branch = sorry)
- Notes: **sorry** — the surjectivity half is an open obligation (deferred §13 cyclic-module density).

### theorem iwasawa_theorem
- Type: `(hp2 : p ≠ 2) : Nonempty (Additive (↥(unitsTower1Plus p) ⧸ (cycloTower1Plus p).subgroupOf (unitsTower1Plus p)) ≃+ (PadicMeasure p (PadicMeasure.GPlus p) ⧸ PadicMeasure.zetaIdealPlus p hp2))`
- What: (RJW thm:iwasawa 2 (ii), THE MILESTONE) The Coleman map induces an iso `𝒰⁺_{∞,1}/𝒞⁺_{∞,1} ≅ Λ(𝒢⁺)/I(𝒢⁺)ζ_p`.
- How: `MulEquiv.ofBijective` on `colDescentPlusMul` (bijective by `colDescentPlusMul_bijective`), converted to additive (`MulEquiv.toAdditive`).
- Hypotheses: `p ≠ 2`.
- Uses from project: [`unitsTower1Plus`, `cycloTower1Plus`, `PadicMeasure`, `PadicMeasure.GPlus`, `PadicMeasure.zetaIdealPlus`, `colDescentPlusMul`, `colDescentPlusMul_bijective`]
- Used by: unused in file (terminal milestone)
- Visibility: public
- Lines: 890–897 (proof ~2 lines / term)
- Notes: none in body; transitively rests on the `sorry` in `colDescentPlusMul_bijective` (and `mem_ZpOne_of_mem_cycloTower1_cAnti`).

### theorem iwasawa_exact_sequence
- Type: `(hp2 : p ≠ 2) : Nonempty (Additive (↥(unitsTower1 p) ⧸ (cycloTower1 p).subgroupOf (unitsTower1 p)) →+ (PadicMeasure p ℤ_[p]ˣ ⧸ PadicMeasure.zetaIdeal p hp2))`
- What: (RJW thm:iwasawa 2 (i)) The `Λ(𝒢)`-module SES `0 → 𝒰_{∞,1}/𝒞_{∞,1} → Λ(𝒢)/I(𝒢)ζ_p → ℤ_p(1) → 0`, stated as the injection with cokernel `ℤ_p(1)`.
- How: Witnessed by `colDescent` (the additive descent).
- Hypotheses: `p ≠ 2`.
- Uses from project: [`unitsTower1`, `cycloTower1`, `PadicMeasure`, `PadicMeasure.zetaIdeal`, `colDescent`]
- Used by: unused in file (terminal milestone)
- Visibility: public
- Lines: 902–906 (proof 1 line / term)
- Notes: none

---

## File Summary

**Total declarations: 39** — defs: 8 (`ColMul`, `colImageSubgroup`, `cycloGenSubgroup`, `colPreimageZeta`, `elemsMonoidHom`, `colDescentMul`, `colDescent`, `ColPlusMul`, `colDescentPlusMul`, `ePlus` → **9 defs**) — recount: defs = 9; theorems/lemmas = 30; instances/structures/classes/abbrevs/inductives = 0. (Total 39.)

Precisely: 9 defs (`ColMul`, `colImageSubgroup`, `cycloGenSubgroup`, `colPreimageZeta`, `elemsMonoidHom`, `colDescentMul`, `colDescent`, `ColPlusMul`, `colDescentPlusMul`, `ePlus` — note this is 10 names; the list is: ColMul, colImageSubgroup, cycloGenSubgroup, colPreimageZeta, elemsMonoidHom, colDescentMul, colDescent, ColPlusMul, colDescentPlusMul, ePlus = **10 defs**) and **29 theorems**. Total **39**. Zero instances.

**Key API (used by ≥3 decls in this file):**
- `Col_one` — used by ≥8 (ColMul, colImageSubgroup, colPreimageZeta, ColPlusMul, Col_galNCU_wGamma_inv, mem_cycloTower1_of_col_mem_zetaIdeal, col_mem_zetaIdeal_of_mem_cycloTower1, …).
- `col_mem_zetaIdeal_of_mem_cycloTower1` — used by 4 (col_image_cycloTower1_eq_zetaIdeal, col_mem_zetaIdeal_iff_mem_cycloTower1, colDescentMul, colDescentPlusMul).
- `colDescentPlusMul` — used by 3 (colDescentPlusMul_injective, colDescentPlusMul_bijective, iwasawa_theorem).

**Unused in file (terminal milestones or banked-but-not-yet-consumed):** `Col_cyclo_mem_zetaIdeal`, `closure_cycloGenSubgroup_le_cycloTower1`, `col_image_cycloTower1_le_zetaIdeal_of_density` (explicitly superseded), `cycloTower1Plus_le_unitsTower1Plus`, `col_image_cycloTower1_eq_zetaIdeal` (referenced only in docstrings), `col_mem_zetaIdeal_iff_mem_cycloTower1` (referenced only in docstrings), `iwasawa_theorem`, `iwasawa_exact_sequence`.

**Declarations with `sorry` (2):**
1. `mem_ZpOne_of_mem_cycloTower1_cAnti` (lines 500–502) — T1224', the `c`-anti-invariant part of cyclotomic closure is `ℤ_p(1)`.
2. `colDescentPlusMul_bijective` (lines 871–883) — surjectivity branch of the milestone bijectivity (deferred §13 cyclic-module density).
   (Transitive dependents resting on these sorries: `col_mem_zetaIdeal_of_mem_cycloTower1`, `col_image_cycloTower1_eq_zetaIdeal`, `col_mem_zetaIdeal_iff_mem_cycloTower1`, `colDescentMul`, `colDescentPlusMul`, `iwasawa_theorem`; the `→`-direction chain `mem_cycloTower1_of_col_mem_zetaIdeal` and `colDescent`/`iwasawa_exact_sequence` are axiom-clean.)

**`set_option`:** none in file.

**Proofs >50 lines (OVER-50): 0.**

**Proofs 30–50 lines (long(30-50)): 1.**
- `col_mem_zetaIdeal_of_mem_cycloTower1` (lines 512–559, ~47 lines).

**Near-threshold note:** `zetaIdeal_le_col_image` is ~27 lines (just under 30); `colDescentPlusMul_injective` ~25; `mem_zetaIdeal_of_mem_plusPart_projPlus` ~21 — none flagged.
