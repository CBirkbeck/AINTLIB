# Inline-duplication work-list (scan of 2026-07-29)

Produced by `scratchpad/repeated_haves.py`. Keys on the **statement shape** of an inline
`have`, not on any name — anonymous `have`s are exactly the copies a name-based duplicate
scan cannot see. Filters: statement >=40 chars, `by` proof, >=4 lines, >=3 copies.

**36 real groups, 910 duplicated lines.** (3 further groups — #8, #12, #13 — are
scan artifacts: the regex mis-parsed a `calc` continuation as a `have` statement.)

## The recurring cause

Most of these are **not** missing lemmas — the lemma already exists and was re-proved inline
anyway. Confirmed instances in this list:

* **#19 is literally `algebraMap_s_mul_divByS`** (RelativePieceKeystone.lean:47), inlined 4x
* **#36 duplicates `presheafValue_completeSpace_rightUniformSpace`**
* **#17 is the `hT_pb` companion** of the `hb` family already collapsed via
  `isPowerBounded_invS_of_one_mem_T` (see GOAL.md) — same proofs, second half

So the first move on each group is **grep the tree for an existing named lemma with that
statement**; only write a new one if there genuinely is none. Second move: if a lemma exists
but is unreachable from the copies, compute the transitive import closure and find the
earliest file that all copies can see (this is how the `invS` family was fixed).

## Structural finding: the `RelativePieceKeystone{,Gen,Open}` clone triple

Groups #0, #1, #2, #5, #6, #7, #11, #15 all appear **once in each of the three files**
`RelativePieceKeystone.lean`, `RelativePieceKeystoneGen.lean`, `RelativePieceKeystoneOpen.lean`.
That is a copy-pasted proof preamble (`hF_alg`, `hu`, `hF_div`, `hps`, `hA₀`, `hqt` — same
`have` names, consecutive lines) shared by a base/general/open family. Extracting the shared
helpers is plain dedup and changes no statement. Unifying the three *theorems* would be a
statement change — `/generalise` territory, not this pass.

## Groups, by duplicated-line count

| # | copies | lines | files | statement |
|---|---|---|---|---|
| 0 | 7 | 92 | 4x WedhornCechAcyclicity · 1x RelativePieceKeystone · 1x RelativePieceKeystoneGen | `∀ p ∈ insert D₀.s D₀.T, D₀.coeRingHom (divByS p D₀.s) ∈ (presheafValue_concretePair D₀).A₀` |
| 1 | 10 | 50 | 4x WedhornCechAcyclicity · 2x RelativePieceKeystone · 2x RelativePieceKeystoneGen | `∀ a : A, F (algebraMap A (Localization.Away DI.s) a) = DB.canonicalMap (D₀.canonicalMap a)` |
| 2 | 6 | 48 | 3x WedhornCechAcyclicity · 1x RelativePieceKeystone · 1x RelativePieceKeystoneGen | `∀ p : A, D₀.canonicalMap p = D₀.canonicalMap D₀.s * D₀.coeRingHom (divByS p D₀.s)` |
| 3 | 3 | 46 | 2x TateAlgebraTopology · 1x MvTateAlgebraTopology | `∀ l, ∃ c : P.A₀, c ∈ P.I ^ i ∧ (c : A) = MvPowerSeries.coeff l xy.val` |
| 4 | 3 | 44 | 1x SheafyPair · 1x TateAcyclicity · 1x WedhornCechAcyclicity | `Function.Injective (productRestrictionSub A C)` |
| 5 | 3 | 42 | 1x RelativePieceKeystone · 1x RelativePieceKeystoneGen · 1x RelativePieceKeystoneOpen | `∀ q : A, DB.canonicalMap (D₀.canonicalMap q) = DB.canonicalMap (D₀.canonicalMap t) * DB.coeRing` |
| 6 | 3 | 42 | 1x RelativePieceKeystone · 1x RelativePieceKeystoneGen · 1x RelativePieceKeystoneOpen | `∀ q ∈ insert t T, divByS (D₀.canonicalMap q) DB.s ∈ locSubring DB.P DB.T DB.s` |
| 7 | 4 | 40 | 2x RelativePieceKeystone · 2x RelativePieceKeystoneGen | `rationalOpen E.T E.s = rationalOpen (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).` |
| 9 | 3 | 30 | 1x SpaVObj · 1x StructureSheafStalks · 1x YStalks | `comap D.canonicalMap (comap (restrictionMapHom D D' hsub) w'') = comap D'.canonicalMap w''` |
| 10 | 3 | 27 | 1x Cor832 · 1x IdealLocalizationCompletion · 1x WedhornCechAcyclicity | `(Subring.map D.coeRingHom (locSubring D.P D.T D.s) : Set (presheafValue D)) = ((D.coeRingHom.co` |
| 11 | 3 | 27 | 1x RelativePieceKeystone · 1x RelativePieceKeystoneGen · 1x RelativePieceKeystoneOpen | `∀ (c : A) (z : presheafValue DB), F (algebraMap A (Localization.Away DI.s) c) = F (algebraMap A` |
| 14 | 3 | 27 | 3x ArCompletion | `alocToWittF p F ϖ (algebraMap (Ainf p F) (Aloc p F ϖ) (y : Ainf p F)) = WittVector.teichmuller ` |
| 15 | 3 | 24 | 1x RelativePieceKeystone · 1x RelativePieceKeystoneGen · 1x RelativePieceKeystoneOpen | `∀ c : A, DI.canonicalMap DI.s * DI.coeRingHom (divByS c DI.s) = DI.canonicalMap c` |
| 16 | 4 | 24 | 2x RestrictedLimitSheaf · 2x SheafyPair | `∀ E : ↥C.covers, E.1.IsRational ∧ ∃ i : ι, spaOpen E.1 ⊆ (U i : Set ↥(Spa A A⁺))` |
| 17 | 4 | 21 | 3x LaurentRefinementCore · 1x RestrictionFlatness | `∀ t ∈ (iteratedMinusDatum_B P D₀ f).T, TopologicalRing.IsPowerBounded t` |
| 18 | 3 | 21 | 3x RobbaPresentation | `perfectoidValuation p F (c : F) = perfectoidValuation p F (zb : F) ^ j * perfectoidValuation p ` |
| 19 | 4 | 20 | 2x RelativeDescent · 2x RelativeDescentHuber | `algebraMap A (Localization.Away E.s) E.s * divByS t E.s = algebraMap A (Localization.Away E.s) ` |
| 20 | 4 | 20 | 4x RobbaPresentation | `gB * (((hgu.unit⁻¹ : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ) : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1` |
| 21 | 3 | 18 | 1x Presentation · 1x SheafyBI · 1x UniformizerEquivariance | `{w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) \| wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 w ≤ ε} ∈ nhds (0 ` |
| 22 | 3 | 17 | 1x SpaVObj · 1x StructureSheafStalks · 1x YStalks | `comap D.canonicalMap (comap (restrictionMapHom D D' hsub) w'') ∈ W` |
| 23 | 3 | 17 | 2x StructureSheaf · 1x Wedhorn828 | `∀ (a : A) (x : presheafValue D), e (a • x) = a • e x` |
| 24 | 3 | 17 | 2x Presentation · 1x RestrictionInjective | `x * algebraMap (Ainf p F) (Bloc p F ϖ) (((p : Ainf p F) * teichPi p F ϖ) ^ k) = algebraMap (Ain` |
| 25 | 3 | 15 | 2x Wedhorn828 · 1x Cor832 | `DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D)` |
| 26 | 3 | 15 | 2x TateAlgebraTopology · 1x MvTateAlgebraTopology | `MvPowerSeries.coeff l xy.val = ∑ p ∈ Finset.antidiagonal l, MvPowerSeries.coeff p.1 x.val * MvP` |
| 27 | 3 | 15 | 1x SpaVObj · 1x StructureSheafStalks · 1x YStalks | `(comap (restrictionMapHom D D' hsub) w'').vle b 0` |
| 28 | 3 | 15 | 3x StructurePresheafBundled | `(V : Set ↥(Spa A A⁺)) ⊆ ⋃ W : RangeIndex U, ((W.1 : Opens ↥(Spa A A⁺)) : Set ↥(Spa A A⁺))` |
| 29 | 3 | 15 | 3x ArCompletion | `WittVector.map ((powerBoundedSubring.toSubring F).subtype) (teichPi p F ϖ) = WittVector.teichmu` |
| 30 | 3 | 15 | 3x ArCompletion | `alocToWittF p F ϖ u * WittVector.teichmuller p (ϖF ^ k) = WittVector.map ((powerBoundedSubring.` |
| 31 | 3 | 15 | 2x BigWindows · 1x ChartSpa | `(p : ℚ) ^ ((n : ℤ) + 1) = ((p ^ (n + 1) : ℕ) : ℚ) / ((1 : ℕ) : ℚ)` |
| 32 | 3 | 14 | 1x NonTateRationalOpenHomeomorph · 1x SpaRationalOpenHomeomorph · 1x SpaRationalSubsetCorrespondence | `x ∈ (fun y => u' * (y - x)) ⁻¹' (((presheafValue D)⁺ : Subring (presheafValue D)) : Set (preshe` |
| 33 | 3 | 14 | 2x RobbaPresentation · 1x IntervalRing | `((1 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) = BIPr` |
| 34 | 3 | 14 | 2x RobbaPresentation · 1x IntervalRing | `((0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) = BIPr` |
| 35 | 3 | 13 | 3x SpaQCviaSpvAI | `I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))` |
| 36 | 3 | 12 | 3x LaurentRefinementCore | `@CompleteSpace (presheafValue D₀) (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀))` |
| 37 | 3 | 12 | 1x RelativePieceKeystone · 1x RelativePieceKeystoneGen · 1x RelativePieceKeystoneOpen | `DI.canonicalMap DI.s = DI.canonicalMap D₀.s * DI.canonicalMap t` |
| 38 | 3 | 12 | 3x WedhornCechAcyclicity | `((unitCover_overlapDatum_B D₀ f).s : presheafValue D₀) = D₀.canonicalMap f` |

## Full copy locations

### #0 — 7 copies, 92 duplicated lines

```lean
∀ p ∈ insert D₀.s D₀.T, D₀.coeRingHom (divByS p D₀.s) ∈ (presheafValue_concretePair D₀).A₀
```

* `RelativePieceKeystone.lean:335` — 13L, `have hA₀`
* `RelativePieceKeystoneGen.lean:252` — 13L, `have hA₀`
* `RelativePieceKeystoneOpen.lean:319` — 13L, `have hA₀`
* `WedhornCechAcyclicity.lean:3038` — 14L, `have hA₀`
* `WedhornCechAcyclicity.lean:3720` — 13L, `have hA₀`
* `WedhornCechAcyclicity.lean:4458` — 13L, `have hA₀`
* `WedhornCechAcyclicity.lean:9167` — 13L, `have hA₀`

### #1 — 10 copies, 50 duplicated lines

```lean
∀ a : A, F (algebraMap A (Localization.Away DI.s) a) = DB.canonicalMap (D₀.canonicalMap a)
```

* `RelativePieceKeystone.lean:310` — 5L, `have hF_alg`
* `RelativePieceKeystone.lean:424` — 5L, `have hF_alg`
* `RelativePieceKeystoneGen.lean:227` — 5L, `have hF_alg`
* `RelativePieceKeystoneGen.lean:340` — 5L, `have hF_alg`
* `RelativePieceKeystoneOpen.lean:294` — 5L, `have hF_alg`
* `RelativePieceKeystoneOpen.lean:409` — 5L, `have hF_alg`
* `WedhornCechAcyclicity.lean:3007` — 5L, `have hF_alg`
* `WedhornCechAcyclicity.lean:3118` — 5L, `have hF_alg`
* `WedhornCechAcyclicity.lean:3683` — 5L, `have hF_alg`
* `WedhornCechAcyclicity.lean:3807` — 5L, `have hF_alg`

### #2 — 6 copies, 48 duplicated lines

```lean
∀ p : A, D₀.canonicalMap p = D₀.canonicalMap D₀.s * D₀.coeRingHom (divByS p D₀.s)
```

* `RelativePieceKeystone.lean:327` — 8L, `have hps`
* `RelativePieceKeystoneGen.lean:244` — 8L, `have hps`
* `RelativePieceKeystoneOpen.lean:311` — 8L, `have hps`
* `WedhornCechAcyclicity.lean:3701` — 8L, `have hps`
* `WedhornCechAcyclicity.lean:4450` — 8L, `have hps`
* `WedhornCechAcyclicity.lean:9159` — 8L, `have hps`

### #3 — 3 copies, 46 duplicated lines

```lean
∀ l, ∃ c : P.A₀, c ∈ P.I ^ i ∧ (c : A) = MvPowerSeries.coeff l xy.val
```

* `MvTateAlgebraTopology.lean:457` — 14L, `have hxy_coeff`
* `TateAlgebraTopology.lean:781` — 18L, `have hxy_coeff`
* `TateAlgebraTopology.lean:2143` — 14L, `have hxy_coeff`

### #4 — 3 copies, 44 duplicated lines

```lean
Function.Injective (productRestrictionSub A C)
```

* `SheafyPair.lean:629` — 26L, `have hInj`
* `TateAcyclicity.lean:1038` — 4L, `have hinj`
* `WedhornCechAcyclicity.lean:13282` — 14L, `have h_inj`

### #5 — 3 copies, 42 duplicated lines

```lean
∀ q : A, DB.canonicalMap (D₀.canonicalMap q) = DB.canonicalMap (D₀.canonicalMap t) * DB.coeRingHom (divByS (D₀.canonicalMap q) DB.s)
```

* `RelativePieceKeystone.lean:349` — 14L, `have hqt`
* `RelativePieceKeystoneGen.lean:266` — 14L, `have hqt`
* `RelativePieceKeystoneOpen.lean:333` — 14L, `have hqt`

### #6 — 3 copies, 42 duplicated lines

```lean
∀ q ∈ insert t T, divByS (D₀.canonicalMap q) DB.s ∈ locSubring DB.P DB.T DB.s
```

* `RelativePieceKeystone.lean:364` — 14L, `have hq_mem`
* `RelativePieceKeystoneGen.lean:281` — 14L, `have hq_mem`
* `RelativePieceKeystoneOpen.lean:348` — 14L, `have hq_mem`

### #7 — 4 copies, 40 duplicated lines

```lean
rationalOpen E.T E.s = rationalOpen (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).T (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).s
```

* `RelativePieceKeystone.lean:936` — 10L, `have h_eq`
* `RelativePieceKeystone.lean:969` — 10L, `have h_eq`
* `RelativePieceKeystoneGen.lean:886` — 10L, `have h_eq`
* `RelativePieceKeystoneGen.lean:921` — 10L, `have h_eq`

### #9 — 3 copies, 30 duplicated lines

```lean
comap D.canonicalMap (comap (restrictionMapHom D D' hsub) w'') = comap D'.canonicalMap w''
```

* `SpaVObj.lean:92` — 10L, `have hbaseEq`
* `StructureSheafStalks.lean:1038` — 10L, `have hbaseEq`
* `FarguesFontaine/YStalks.lean:109` — 10L, `have hbaseEq`

### #10 — 3 copies, 27 duplicated lines

```lean
(Subring.map D.coeRingHom (locSubring D.P D.T D.s) : Set (presheafValue D)) = ((D.coeRingHom.comp (locSubring D.P D.T D.s).subtype).range : Set (presheafValue D))
```

* `Cor832.lean:1559` — 8L, `have h_sub_eq`
* `IdealLocalizationCompletion.lean:179` — 7L, `have h_sub_eq`
* `WedhornCechAcyclicity.lean:7391` — 12L, `have h_sub_eq`

### #11 — 3 copies, 27 duplicated lines

```lean
∀ (c : A) (z : presheafValue DB), F (algebraMap A (Localization.Away DI.s) c) = F (algebraMap A (Localization.Away DI.s) DI.s) * z → F (divByS c DI.s) = z
```

* `RelativePieceKeystone.lean:318` — 9L, `have hF_div`
* `RelativePieceKeystoneGen.lean:235` — 9L, `have hF_div`
* `RelativePieceKeystoneOpen.lean:302` — 9L, `have hF_div`

### #14 — 3 copies, 27 duplicated lines

```lean
alocToWittF p F ϖ (algebraMap (Ainf p F) (Aloc p F ϖ) (y : Ainf p F)) = WittVector.teichmuller p (ϖF ^ k)
```

* `FarguesFontaine/ArCompletion.lean:225` — 9L, `have hy`
* `FarguesFontaine/ArCompletion.lean:300` — 9L, `have hy`
* `FarguesFontaine/ArCompletion.lean:1324` — 9L, `have hy`

### #15 — 3 copies, 24 duplicated lines

```lean
∀ c : A, DI.canonicalMap DI.s * DI.coeRingHom (divByS c DI.s) = DI.canonicalMap c
```

* `RelativePieceKeystone.lean:540` — 8L, `have hchase`
* `RelativePieceKeystoneGen.lean:468` — 8L, `have hchase`
* `RelativePieceKeystoneOpen.lean:549` — 8L, `have hchase`

### #16 — 4 copies, 24 duplicated lines

```lean
∀ E : ↥C.covers, E.1.IsRational ∧ ∃ i : ι, spaOpen E.1 ⊆ (U i : Set ↥(Spa A A⁺))
```

* `RestrictedLimitSheaf.lean:253` — 6L, `have hexE`
* `RestrictedLimitSheaf.lean:389` — 6L, `have hexE`
* `SheafyPair.lean:283` — 6L, `have hexE`
* `SheafyPair.lean:458` — 6L, `have hexE`

### #17 — 4 copies, 21 duplicated lines

```lean
∀ t ∈ (iteratedMinusDatum_B P D₀ f).T, TopologicalRing.IsPowerBounded t
```

* `LaurentRefinementCore.lean:2964` — 5L, `have hT_pb`
* `LaurentRefinementCore.lean:3265` — 5L, `have hT_pb`
* `LaurentRefinementCore.lean:3455` — 5L, `have hT_pb`
* `RestrictionFlatness.lean:131` — 6L, `have hT_pb`

### #18 — 3 copies, 21 duplicated lines

```lean
perfectoidValuation p F (c : F) = perfectoidValuation p F (zb : F) ^ j * perfectoidValuation p F (c' : F)
```

* `FarguesFontaine/RobbaPresentation.lean:1041` — 7L, `have hval`
* `FarguesFontaine/RobbaPresentation.lean:1087` — 7L, `have hval`
* `FarguesFontaine/RobbaPresentation.lean:1203` — 7L, `have hval`

### #19 — 4 copies, 20 duplicated lines

```lean
algebraMap A (Localization.Away E.s) E.s * divByS t E.s = algebraMap A (Localization.Away E.s) t
```

* `RelativeDescent.lean:229` — 5L, `have hspec`
* `RelativeDescent.lean:396` — 5L, `have hspecA`
* `RelativeDescentHuber.lean:141` — 5L, `have hspec`
* `RelativeDescentHuber.lean:309` — 5L, `have hspecA`

### #20 — 4 copies, 20 duplicated lines

```lean
gB * (((hgu.unit⁻¹ : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ) : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))) = 1
```

* `FarguesFontaine/RobbaPresentation.lean:3010` — 5L, `have hinv`
* `FarguesFontaine/RobbaPresentation.lean:3041` — 5L, `have hinv`
* `FarguesFontaine/RobbaPresentation.lean:3170` — 5L, `have hinvS`
* `FarguesFontaine/RobbaPresentation.lean:4135` — 5L, `have hinvS`

### #21 — 3 copies, 18 duplicated lines

```lean
{w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) | wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 w ≤ ε} ∈ nhds (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
```

* `FarguesFontaine/Presentation.lean:2279` — 6L, `have hball`
* `FarguesFontaine/SheafyBI.lean:55` — 6L, `have hball`
* `FarguesFontaine/UniformizerEquivariance.lean:316` — 6L, `have hnhd`

### #22 — 3 copies, 17 duplicated lines

```lean
comap D.canonicalMap (comap (restrictionMapHom D D' hsub) w'') ∈ W
```

* `SpaVObj.lean:102` — 6L, `have hW'`
* `StructureSheafStalks.lean:1048` — 5L, `have hW'`
* `FarguesFontaine/YStalks.lean:119` — 6L, `have hW'`

### #23 — 3 copies, 17 duplicated lines

```lean
∀ (a : A) (x : presheafValue D), e (a • x) = a • e x
```

* `StructureSheaf.lean:1017` — 5L, `have he_smul`
* `StructureSheaf.lean:1067` — 6L, `have he_smul`
* `Wedhorn828.lean:845` — 6L, `have he_smul`

### #24 — 3 copies, 17 duplicated lines

```lean
x * algebraMap (Ainf p F) (Bloc p F ϖ) (((p : Ainf p F) * teichPi p F ϖ) ^ k) = algebraMap (Ainf p F) (Bloc p F ϖ) a
```

* `FarguesFontaine/Presentation.lean:1651` — 6L, `have hxy'`
* `FarguesFontaine/Presentation.lean:1988` — 6L, `have hxy'`
* `FarguesFontaine/RestrictionInjective.lean:209` — 5L, `have h1`

### #25 — 3 copies, 15 duplicated lines

```lean
DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D)
```

* `Cor832.lean:2061` — 5L, `have hdense`
* `Wedhorn828.lean:1385` — 4L, `have hdense`
* `Wedhorn828.lean:2066` — 6L, `have hdense`

### #26 — 3 copies, 15 duplicated lines

```lean
MvPowerSeries.coeff l xy.val = ∑ p ∈ Finset.antidiagonal l, MvPowerSeries.coeff p.1 x.val * MvPowerSeries.coeff p.2 y.val.val
```

* `MvTateAlgebraTopology.lean:460` — 5L, `have hcoeff`
* `TateAlgebraTopology.lean:785` — 5L, `have hcoeff`
* `TateAlgebraTopology.lean:2146` — 5L, `have hcoeff`

### #27 — 3 copies, 15 duplicated lines

```lean
(comap (restrictionMapHom D D' hsub) w'').vle b 0
```

* `SpaVObj.lean:112` — 5L, `have hcb`
* `StructureSheafStalks.lean:1058` — 5L, `have hcb`
* `FarguesFontaine/YStalks.lean:129` — 5L, `have hcb`

### #28 — 3 copies, 15 duplicated lines

```lean
(V : Set ↥(Spa A A⁺)) ⊆ ⋃ W : RangeIndex U, ((W.1 : Opens ↥(Spa A A⁺)) : Set ↥(Spa A A⁺))
```

* `StructurePresheafBundled.lean:164` — 5L, `have hcov'`
* `StructurePresheafBundled.lean:197` — 5L, `have hcov'`
* `StructurePresheafBundled.lean:246` — 5L, `have hcov'`

### #29 — 3 copies, 15 duplicated lines

```lean
WittVector.map ((powerBoundedSubring.toSubring F).subtype) (teichPi p F ϖ) = WittVector.teichmuller p ϖF
```

* `FarguesFontaine/ArCompletion.lean:228` — 5L, `have hone`
* `FarguesFontaine/ArCompletion.lean:303` — 5L, `have hone`
* `FarguesFontaine/ArCompletion.lean:1327` — 5L, `have hone`

### #30 — 3 copies, 15 duplicated lines

```lean
alocToWittF p F ϖ u * WittVector.teichmuller p (ϖF ^ k) = WittVector.map ((powerBoundedSubring.toSubring F).subtype) a
```

* `FarguesFontaine/ArCompletion.lean:234` — 5L, `have himg`
* `FarguesFontaine/ArCompletion.lean:309` — 5L, `have himg`
* `FarguesFontaine/ArCompletion.lean:1333` — 5L, `have himg`

### #31 — 3 copies, 15 duplicated lines

```lean
(p : ℚ) ^ ((n : ℤ) + 1) = ((p ^ (n + 1) : ℕ) : ℚ) / ((1 : ℕ) : ℚ)
```

* `FarguesFontaine/BigWindows.lean:164` — 5L, `have hab2`
* `FarguesFontaine/BigWindows.lean:299` — 5L, `have hab`
* `FarguesFontaine/ChartSpa.lean:253` — 5L, `have hab`

### #32 — 3 copies, 14 duplicated lines

```lean
x ∈ (fun y => u' * (y - x)) ⁻¹' (((presheafValue D)⁺ : Subring (presheafValue D)) : Set (presheafValue D))
```

* `NonTateRationalOpenHomeomorph.lean:79` — 5L, `have hxO`
* `SpaRationalOpenHomeomorph.lean:262` — 5L, `have hxO`
* `SpaRationalSubsetCorrespondence.lean:112` — 4L, `have hxO`

### #33 — 3 copies, 14 duplicated lines

```lean
((1 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 1
```

* `FarguesFontaine/IntervalRing.lean:1002` — 4L, `have hone`
* `FarguesFontaine/RobbaPresentation.lean:3887` — 5L, `have hone`
* `FarguesFontaine/RobbaPresentation.lean:5459` — 5L, `have hone`

### #34 — 3 copies, 14 duplicated lines

```lean
((0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 0
```

* `FarguesFontaine/IntervalRing.lean:1024` — 4L, `have hzero`
* `FarguesFontaine/RobbaPresentation.lean:3907` — 5L, `have hzero`
* `FarguesFontaine/RobbaPresentation.lean:5480` — 5L, `have hzero`

### #35 — 3 copies, 13 duplicated lines

```lean
I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))
```

* `SpaQCviaSpvAI.lean:780` — 4L, `have hIeq'`
* `SpaQCviaSpvAI.lean:822` — 4L, `have hIeq'`
* `SpaQCviaSpvAI.lean:1097` — 5L, `have hIeq'`

### #36 — 3 copies, 12 duplicated lines

```lean
@CompleteSpace (presheafValue D₀) (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀))
```

* `LaurentRefinementCore.lean:2972` — 4L, `have hA_complete`
* `LaurentRefinementCore.lean:3270` — 4L, `have hA_complete`
* `LaurentRefinementCore.lean:3460` — 4L, `have hA_complete`

### #37 — 3 copies, 12 duplicated lines

```lean
DI.canonicalMap DI.s = DI.canonicalMap D₀.s * DI.canonicalMap t
```

* `RelativePieceKeystone.lean:548` — 4L, `have hsplit`
* `RelativePieceKeystoneGen.lean:476` — 4L, `have hsplit`
* `RelativePieceKeystoneOpen.lean:557` — 4L, `have hsplit`

### #38 — 3 copies, 12 duplicated lines

```lean
((unitCover_overlapDatum_B D₀ f).s : presheafValue D₀) = D₀.canonicalMap f
```

* `WedhornCechAcyclicity.lean:4484` — 4L, `have heq_s`
* `WedhornCechAcyclicity.lean:6339` — 4L, `have heq_s`
* `WedhornCechAcyclicity.lean:6692` — 4L, `have heq_s`

