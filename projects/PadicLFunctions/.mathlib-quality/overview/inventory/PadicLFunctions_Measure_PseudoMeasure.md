# Inventory: PadicLFunctions/Measure/PseudoMeasure.lean

File-level: `namespace PadicMeasure`; `variable (p : ℕ) [hp : Fact p.Prime]`; whole file inside `noncomputable section`. RJW arXiv:2309.15692 §3.6 (convolution algebra Λ(ℤ_p^×), pseudo-measures). Imports project files `Measure.UnitsZp`, `Measure.Fubini`.

---

### def mulCM₂
- Type: `def mulCM₂ : C(G × G, G) := ⟨fun q => q.1 * q.2, continuous_mul⟩` (for `G` compact comm. top. monoid)
- What: Multiplication on a topological monoid `G` packaged as a single continuous map `G × G → G`.
- How: Direct bundling of `(· * ·)` with the `continuous_mul` proof of continuity.
- Hypotheses: `G` is a `TopologicalSpace`, `CommMonoid`, `ContinuousMul`, `CompactSpace`.
- Uses from project: []
- Used by: `conv`, `unitsMulCM₂`, and the `CommRing` instance, `deg`.
- Visibility: public
- Lines: 49 (proof: term, 1 line)
- Notes: none

### def conv
- Type: `noncomputable def conv (μ ν : PadicMeasure p G) : PadicMeasure p G` with `toFun f := μ (innerInt p ν (f.comp (mulCM₂ G)))`
- What: The convolution of two measures on a compact commutative monoid `G`, defined by `∫ f d(μ⋆ν) = ∫(∫ f(xy) dν(y)) dμ(x)` (RJW Eq. (3.11)).
- How: Builds the `PadicMeasure` (a linear map) by composing `f` with multiplication, taking the inner integral against `ν`, then applying `μ`; additivity/`smul` follow from `ContinuousMap.add_comp`/`smul_comp` plus `innerInt_add`/`innerInt_smul`.
- Hypotheses: `G` compact comm. top. monoid; `μ, ν` measures on `G`.
- Uses from project: [`PadicMeasure`, `innerInt`, `innerInt_add`, `innerInt_smul`]
- Used by: `Mul` instance, `conv_mul_def`, `conv_mul_apply`, `unitsConv`, `CommRing` instance.
- Visibility: public
- Lines: 57-60 (proof: 2 fields, ~2 lines)
- Notes: none

### instance Mul (PadicMeasure p G)
- Type: `noncomputable instance : Mul (PadicMeasure p G) := ⟨conv p⟩`
- What: Multiplication on measures is convolution.
- How: Wraps `conv p`.
- Hypotheses: `G` compact comm. top. monoid.
- Uses from project: [`PadicMeasure`, `conv`]
- Used by: `conv_mul_def`, `conv_mul_apply`, the `CommRing` instance, all downstream `*`.
- Visibility: public
- Lines: 62 (term)
- Notes: none

### instance One (PadicMeasure p G)
- Type: `noncomputable instance : One (PadicMeasure p G) := ⟨dirac p 1⟩`
- What: The multiplicative unit measure is the Dirac measure at the monoid identity `1`.
- How: Wraps `dirac p 1`.
- Hypotheses: `G` compact comm. top. monoid.
- Uses from project: [`PadicMeasure`, `dirac`]
- Used by: `conv_one_def`, `CommRing` instance, `deg`.
- Visibility: public
- Lines: 64 (term)
- Notes: none

### lemma conv_mul_def
- Type: `lemma conv_mul_def (μ ν : PadicMeasure p G) : μ * ν = conv p μ ν := rfl`
- What: The ring multiplication on measures unfolds definitionally to `conv`.
- How: `rfl`.
- Hypotheses: `G` compact comm. top. monoid; `μ, ν` measures.
- Uses from project: [`PadicMeasure`, `conv`]
- Used by: unused in file
- Visibility: public
- Lines: 66 (rfl)
- Notes: none

### lemma conv_mul_apply
- Type: `@[simp] lemma conv_mul_apply (μ ν) (f : C(G, ℤ_[p])) : (μ * ν) f = μ (innerInt p ν (f.comp (mulCM₂ G))) := rfl`
- What: Evaluating a convolution product at a test function equals the iterated-integral formula.
- How: `rfl`.
- Hypotheses: `G` compact comm. top. monoid.
- Uses from project: [`PadicMeasure`, `innerInt`, `mulCM₂`]
- Used by: unused in file
- Visibility: public (simp)
- Lines: 68-70 (rfl)
- Notes: none

### lemma conv_one_def
- Type: `lemma conv_one_def : (1 : PadicMeasure p G) = dirac p 1 := rfl` (with `omit [ContinuousMul G] [CompactSpace G]`)
- What: The unit measure is the Dirac at `1`.
- How: `rfl`; omits the continuity/compactness instances.
- Hypotheses: `G` comm. top. monoid (continuity/compactness omitted).
- Uses from project: [`PadicMeasure`, `dirac`]
- Used by: unused in file
- Visibility: public
- Lines: 72-73 (rfl)
- Notes: none

### instance CommRing (PadicMeasure p G)
- Type: `noncomputable instance : CommRing (PadicMeasure p G)` (full ring-axiom record)
- What: The Iwasawa algebra `Λ(G) = ℳ(G, ℤ_p)` is a commutative ring under convolution.
- How: Each axiom is proved by `LinearMap.ext`, reducing to pointwise identities on `G`: `mul_assoc` from triple-integral reassociation via `mul_assoc` in `G`; `mul_comm` from the Fubini swap `integral_swap` plus `mul_comm`; distributivity/zero laws from `innerInt_measure_add`/`innerInt_measure_zero`; units from `one_mul`/`mul_one`.
- Hypotheses: `G` compact comm. top. monoid.
- Uses from project: [`PadicMeasure`, `conv`, `innerInt`, `mulCM₂`, `dirac`, `integral_swap`, `innerInt_measure_add`, `innerInt_measure_zero`]
- Used by: implicitly all later ring algebra (products, `deg`, `levelMap`, `nonZeroDivisors`, `FractionRing`).
- Visibility: public
- Lines: 81-135 (proof: ~55 lines)
- Notes: OVER-50 (needs /decompose-proof); the proof is a record of ~9 axiom subproofs, each short, but the aggregate body exceeds 50 lines.

### theorem conv_dirac_mul_dirac
- Type: `@[simp] theorem conv_dirac_mul_dirac (u v : G) : (dirac p u) * dirac p v = dirac p (u * v)`
- What: Convolution of two Dirac measures is the Dirac at the product of the points.
- How: `LinearMap.ext fun _f => rfl`.
- Hypotheses: `G` compact comm. top. monoid; `u, v ∈ G`.
- Uses from project: [`PadicMeasure`, `dirac`]
- Used by: `units_dirac_mul_dirac`.
- Visibility: public (simp)
- Lines: 137-140 (proof: 1 line)
- Notes: none

### def deg
- Type: `noncomputable def deg : PadicMeasure p G →+* ℤ_[p]` with `toFun μ := μ 1`
- What: The degree/augmentation ring homomorphism `Λ(G) → ℤ_p`, `μ ↦ ∫_G 1 dμ` (evaluation at the constant function 1).
- How: Ring-hom fields: `map_one'`/`map_zero'`/`map_add'` are `rfl`; `map_mul'` rewrites the inner integral of the constant 1 as `ν 1 • 1` via a `curry` identity, then `map_smul` + `mul_comm`.
- Hypotheses: `G` compact comm. top. monoid.
- Uses from project: [`PadicMeasure`, `innerInt`, `mulCM₂`, `dirac` (via One)]
- Used by: `augmentationIdeal`, `sum_levelMap_coeff`, `augmentationIdeal_eq_span`, `isPseudoMeasure_mk'`.
- Visibility: public
- Lines: 148-165 (proof: ~17 lines)
- Notes: long(30-50)? No — proof body ~17 lines; none.

### def augmentationIdeal
- Type: `noncomputable def augmentationIdeal : Ideal (PadicMeasure p G) := RingHom.ker (deg p)`
- What: The augmentation ideal `I(G) = ker(deg)` of the Iwasawa algebra.
- How: Kernel of the degree map.
- Hypotheses: `G` compact comm. top. monoid.
- Uses from project: [`PadicMeasure`, `deg`]
- Used by: `augmentationIdeal_eq_span`, `isPseudoMeasure_mk'`.
- Visibility: public
- Lines: 167-169 (def)
- Notes: none

### abbrev unitsMulCM₂
- Type: `abbrev unitsMulCM₂ : C(ℤ_[p]ˣ × ℤ_[p]ˣ, ℤ_[p]ˣ) := mulCM₂ ℤ_[p]ˣ`
- What: Multiplication on `ℤ_p^×` as a continuous map (specialisation of `mulCM₂`).
- How: Abbreviation specialising `mulCM₂` to `G = ℤ_[p]ˣ`.
- Hypotheses: none beyond ambient `p` prime.
- Uses from project: [`mulCM₂`]
- Used by: `units_mul_apply`, `levelMap` (map_mul'), `dirac_sub_one_mul_apply`, `units_mul_apply_unitsPowCM`, `augmentationIdeal_eq_span`.
- Visibility: public
- Lines: 182 (abbrev)
- Notes: none

### abbrev unitsConv
- Type: `noncomputable abbrev unitsConv (μ ν : PadicMeasure p ℤ_[p]ˣ) : PadicMeasure p ℤ_[p]ˣ := conv p μ ν`
- What: Convolution on `ℤ_p^×`-measures (specialisation of `conv`).
- How: Abbreviation of `conv p`.
- Hypotheses: `μ, ν` measures on `ℤ_p^×`.
- Uses from project: [`PadicMeasure`, `conv`]
- Used by: `units_mul_def`.
- Visibility: public
- Lines: 188-189 (abbrev)
- Notes: none

### lemma units_mul_def
- Type: `lemma units_mul_def (μ ν : PadicMeasure p ℤ_[p]ˣ) : μ * ν = unitsConv p μ ν := rfl`
- What: Multiplication of `ℤ_p^×`-measures is `unitsConv`.
- How: `rfl`.
- Hypotheses: `μ, ν` measures on `ℤ_p^×`.
- Uses from project: [`PadicMeasure`, `unitsConv`]
- Used by: unused in file
- Visibility: public
- Lines: 191 (rfl)
- Notes: none

### lemma units_mul_apply
- Type: `@[simp] lemma units_mul_apply (μ ν) (f : C(ℤ_[p]ˣ, ℤ_[p])) : (μ * ν) f = μ (innerInt p ν (f.comp (unitsMulCM₂ p))) := rfl`
- What: Evaluation of a `ℤ_p^×`-convolution at a test function.
- How: `rfl`.
- Hypotheses: `μ, ν` measures on `ℤ_p^×`.
- Uses from project: [`PadicMeasure`, `innerInt`, `unitsMulCM₂`]
- Used by: `levelMap` (map_mul'), `units_mul_apply_unitsPowCM`.
- Visibility: public (simp)
- Lines: 193-195 (rfl)
- Notes: none

### lemma units_one_def
- Type: `lemma units_one_def : (1 : PadicMeasure p ℤ_[p]ˣ) = dirac p 1 := rfl`
- What: The unit `ℤ_p^×`-measure is the Dirac at 1.
- How: `rfl`.
- Hypotheses: none beyond `p` prime.
- Uses from project: [`PadicMeasure`, `dirac`]
- Used by: `levelMap` (map_one'), `dirac_sub_one_mul_apply`, `dirac_sub_one_mem_nonZeroDivisors`.
- Visibility: public
- Lines: 197 (rfl)
- Notes: none

### theorem units_dirac_mul_dirac
- Type: `@[simp] theorem units_dirac_mul_dirac (u v : ℤ_[p]ˣ) : (dirac p u) * dirac p v = dirac p (u * v) := conv_dirac_mul_dirac p u v`
- What: Convolution of Dirac measures on `ℤ_p^×`.
- How: Direct application of `conv_dirac_mul_dirac`.
- Hypotheses: `u, v ∈ ℤ_p^×`.
- Uses from project: [`PadicMeasure`, `dirac`, `conv_dirac_mul_dirac`]
- Used by: unused in file
- Visibility: public (simp)
- Lines: 199-202 (term)
- Notes: none

### def unitsToZModPow
- Type: `noncomputable def unitsToZModPow (n : ℕ) : ℤ_[p]ˣ →* (ZMod (p ^ n))ˣ := Units.map (PadicInt.toZModPow n).toMonoidHom`
- What: The reduction homomorphism `ℤ_p^× → (ℤ/p^n)^×`, the units functor applied to `PadicInt.toZModPow`.
- How: `Units.map` of the underlying ring reduction.
- Hypotheses: `n : ℕ`.
- Uses from project: []
- Used by: nearly the entire `finiteLevel`/`augmentation` apparatus (`unitsToZModPow_coe`, fiber lemmas, `levelChar`, `levelMap`, `exists_topological_generator`, …).
- Visibility: public
- Lines: 209-210 (def)
- Notes: none

### lemma unitsToZModPow_coe
- Type: `@[simp] lemma unitsToZModPow_coe (n) (u : ℤ_[p]ˣ) : ((unitsToZModPow p n u : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) = PadicInt.toZModPow n (u : ℤ_[p]) := rfl`
- What: The underlying residue of `unitsToZModPow n u` is the ring reduction of `u`.
- How: `rfl`.
- Hypotheses: `n : ℕ`, `u ∈ ℤ_p^×`.
- Uses from project: [`unitsToZModPow`]
- Used by: `unitsToZModPow_surjective`.
- Visibility: public (simp)
- Lines: 212-215 (rfl)
- Notes: none

### lemma isClopen_toZModPow_fiber
- Type: `lemma isClopen_toZModPow_fiber (n) (a : ZMod (p ^ n)) : IsClopen {z : ℤ_[p] | PadicInt.toZModPow n z = a}`
- What: Each residue disc `{z | z ≡ a mod p^n}` is clopen in `ℤ_p`.
- How: Openness is `isOpen_toZModPow_fiber`; closedness via complement being a finite union of the other fibers (`isOpen_biUnion`).
- Hypotheses: `n : ℕ`, `a : ZMod (p^n)`.
- Uses from project: [] (uses mathlib `isOpen_toZModPow_fiber`)
- Used by: `isClopen_unitsToZModPow_fiber`.
- Visibility: public
- Lines: 217-230 (proof: ~12 lines)
- Notes: none

### lemma isClopen_unitsToZModPow_fiber
- Type: `lemma isClopen_unitsToZModPow_fiber (n) (g : (ZMod (p ^ n))ˣ) : IsClopen (unitsToZModPow p n ⁻¹' {g})`
- What: The fiber of the reduction `unitsToZModPow n` over a residue `g` is clopen in `ℤ_p^×`.
- How: Rewrites the fiber as the `Units.val`-preimage of the ring-level residue disc, then transports clopenness via `IsClopen.preimage` along the continuous coercion `Units.continuous_val`.
- Hypotheses: `n : ℕ`, `g : (ZMod (p^n))ˣ`.
- Uses from project: [`unitsToZModPow`, `isClopen_toZModPow_fiber`]
- Used by: `levelChar`, `exists_level_factorization`, `exists_topological_generator`.
- Visibility: public
- Lines: 232-241 (proof: ~9 lines)
- Notes: none

### def levelChar
- Type: `noncomputable def levelChar (n) (g : (ZMod (p ^ n))ˣ) : C(ℤ_[p]ˣ, ℤ_[p])`
- What: The indicator function of the level-`n` residue disc `{u | unitsToZModPow n u = g}`, as a continuous map `ℤ_p^× → ℤ_p`.
- How: The `charFn` of the clopen fiber `isClopen_unitsToZModPow_fiber`, coerced to a continuous map.
- Hypotheses: `n : ℕ`, `g : (ZMod (p^n))ˣ`.
- Uses from project: [`unitsToZModPow`, `isClopen_unitsToZModPow_fiber`]
- Used by: `levelChar_apply_eq/ne`, `levelMap`, `sum_levelChar`, and ubiquitously thereafter.
- Visibility: public
- Lines: 243-245 (def)
- Notes: none

### lemma levelChar_apply_eq
- Type: `lemma levelChar_apply_eq {n g u} (h : unitsToZModPow p n u = g) : levelChar p n g u = 1`
- What: The level indicator evaluates to 1 on points of its disc.
- How: Unfolds `charFn` to `Set.indicator`; `Set.indicator_of_mem` gives 1.
- Hypotheses: `unitsToZModPow n u = g`.
- Uses from project: [`levelChar`, `unitsToZModPow`]
- Used by: `levelMap`, `sum_levelChar`, `levelMap_dirac`, `levelMap_jointly_injective`, `sum_levelChar_fiber`.
- Visibility: public
- Lines: 247-250 (proof: ~3 lines)
- Notes: none

### lemma levelChar_apply_ne
- Type: `lemma levelChar_apply_ne {n g u} (h : unitsToZModPow p n u ≠ g) : levelChar p n g u = 0`
- What: The level indicator evaluates to 0 off its disc.
- How: `Set.indicator_of_notMem`.
- Hypotheses: `unitsToZModPow n u ≠ g`.
- Uses from project: [`levelChar`, `unitsToZModPow`]
- Used by: `levelMap`, `sum_levelChar`, `levelMap_dirac`, `levelMap_jointly_injective`, `sum_levelChar_fiber`.
- Visibility: public
- Lines: 252-255 (proof: ~3 lines)
- Notes: none

### def levelMap
- Type: `noncomputable def levelMap (n) : PadicMeasure p ℤ_[p]ˣ →+* MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ` with `toFun μ := ∑ g, MonoidAlgebra.single g (μ (levelChar p n g))`
- What: The finite-level ring map `Λ(ℤ_p^×) → ℤ_p[(ℤ/p^n)^×]` sending a measure to `∑_g μ(𝟙_{g-fibre})·[g]`; the inverse limit of these is the Iwasawa algebra.
- How: Ring-hom record. `map_one'` isolates the `g=1` term via `Finset.sum_eq_single`. `map_mul'` is the hard field: a `curry` identity rewrites the inner integral of a level indicator as a level indicator (`hcurry`), hence the convolution against an indicator is a finite sum (`hconv`); then expands the product of two group-ring sums with `Finset.sum_mul_sum` + `MonoidAlgebra.single_mul_single`, reindexing via `Fintype.sum_equiv (Equiv.mulLeft g)` and `Finset.sum_comm`. `map_zero'`/`map_add'` from `MonoidAlgebra.single_zero/_add`.
- Hypotheses: `n : ℕ`; uses `[hp : Fact p.Prime]`.
- Uses from project: [`PadicMeasure`, `levelChar`, `unitsToZModPow`, `levelChar_apply_eq`, `levelChar_apply_ne`, `units_mul_apply`, `unitsMulCM₂`, `innerInt`, `units_one_def`, `dirac`, `dirac_apply`]
- Used by: `levelMap_apply_coeff`, `levelMap_eq_zero_iff`, `levelMap_dirac`, `levelMap_smul`, `mapDomain_levelMap`, `sum_levelMap_coeff`, `levelMap_jointly_injective`, `augmentationIdeal_eq_span`.
- Visibility: public
- Lines: 262-351 (proof: ~89 lines)
- Notes: OVER-50 (needs /decompose-proof); `map_mul'` alone is ~67 lines with nested `have hcurry`/`hconv`/`calc`. Hinges on `MonoidAlgebra.single_mul_single`, `Finset.sum_mul_sum`, `Fintype.sum_equiv (Equiv.mulLeft g)`.

### lemma levelMap_apply_coeff
- Type: `lemma levelMap_apply_coeff (n) (μ) (g : (ZMod (p ^ n))ˣ) : (levelMap p n μ) g = μ (levelChar p n g)`
- What: The `g`-coefficient of `levelMap n μ` is the measure of the `g`-disc.
- How: Pushes coefficient extraction `Finsupp.applyAddHom g` through the sum, then `MonoidAlgebra.single_apply` + `Finset.sum_ite_eq'`.
- Hypotheses: `n : ℕ`, `μ` measure, `g` residue.
- Uses from project: [`levelMap`, `levelChar`]
- Used by: `levelMap_eq_zero_iff`, `sum_levelMap_coeff`.
- Visibility: public
- Lines: 353-362 (proof: ~7 lines)
- Notes: none

### lemma levelMap_eq_zero_iff
- Type: `lemma levelMap_eq_zero_iff (n) (μ) : levelMap p n μ = 0 ↔ ∀ g, μ (levelChar p n g) = 0`
- What: `levelMap n μ` vanishes iff `μ` has measure 0 on every level-`n` disc.
- How: Forward via `levelMap_apply_coeff` per coefficient; backward via `Finset.sum_eq_zero` + `MonoidAlgebra.single_zero`.
- Hypotheses: `n : ℕ`, `μ` measure.
- Uses from project: [`levelMap`, `levelMap_apply_coeff`, `levelChar`]
- Used by: `levelMap_jointly_injective`, `augmentationIdeal_eq_span` (via `hSmem`).
- Visibility: public
- Lines: 364-372 (proof: ~9 lines)
- Notes: none

### lemma sum_levelChar
- Type: `lemma sum_levelChar (n) : (∑ g, levelChar p n g) = (1 : C(ℤ_[p]ˣ, ℤ_[p]))`
- What: The level-`n` indicators partition `ℤ_p^×`: they sum to the constant 1.
- How: Pointwise; `Finset.sum_eq_single (unitsToZModPow p n u)` isolates the disc containing `u` via `levelChar_apply_eq/ne`.
- Hypotheses: `n : ℕ`.
- Uses from project: [`levelChar`, `unitsToZModPow`, `levelChar_apply_eq`, `levelChar_apply_ne`]
- Used by: `sum_levelMap_coeff`, `augmentationIdeal_eq_span` (the `n=0` case).
- Visibility: public
- Lines: 374-383 (proof: ~8 lines)
- Notes: none

### lemma levelMap_dirac
- Type: `lemma levelMap_dirac (n) (u : ℤ_[p]ˣ) : levelMap p n (dirac p u) = MonoidAlgebra.single (unitsToZModPow p n u) 1`
- What: `levelMap` of a Dirac measure is the single basis element at the reduction of `u`.
- How: `Finset.sum_eq_single (unitsToZModPow p n u)` with `dirac_apply` and `levelChar_apply_eq/ne`.
- Hypotheses: `n : ℕ`, `u ∈ ℤ_p^×`.
- Uses from project: [`levelMap`, `dirac`, `dirac_apply`, `levelChar`, `unitsToZModPow`, `levelChar_apply_eq`, `levelChar_apply_ne`]
- Used by: `augmentationIdeal_eq_span` (the `hSne` construction, twice).
- Visibility: public
- Lines: 385-392 (proof: ~7 lines)
- Notes: none

### lemma levelMap_smul
- Type: `lemma levelMap_smul (n) (c : ℤ_[p]) (μ) : levelMap p n (c • μ) = c • levelMap p n μ`
- What: `levelMap` is `ℤ_p`-linear (commutes with scalar multiplication).
- How: `Finset.smul_sum` then per-term `MonoidAlgebra.smul_single`.
- Hypotheses: `n : ℕ`, `c : ℤ_[p]`, `μ` measure.
- Uses from project: [`levelMap`, `levelChar`]
- Used by: `augmentationIdeal_eq_span` (`hlev`).
- Visibility: public
- Lines: 394-400 (proof: ~6 lines)
- Notes: none

### lemma unitsToZModPow_le
- Type: `lemma unitsToZModPow_le {n m} (h : n ≤ m) (a : ℤ_[p]ˣ) : unitsToZModPow p n a = ZMod.unitsMap (pow_dvd_pow p h) (unitsToZModPow p m a)`
- What: Compatibility of reductions: level `n` factors through level `m ≥ n` via `ZMod.unitsMap`.
- How: `Units.ext` reduces to ring level; `PadicInt.zmod_cast_comp_toZModPow` gives the cast-compatibility.
- Hypotheses: `n ≤ m`, `a ∈ ℤ_p^×`.
- Uses from project: [`unitsToZModPow`]
- Used by: `exists_level_factorization`, `sum_levelChar_fiber`, `mapDomain_levelMap`, `exists_topological_generator`.
- Visibility: public
- Lines: 402-409 (proof: ~5 lines)
- Notes: none

### lemma unitsToZModPow_surjective
- Type: `lemma unitsToZModPow_surjective (n) (hn : 0 < n) : Function.Surjective (unitsToZModPow p n)`
- What: The reduction `ℤ_p^× → (ℤ/p^n)^×` is surjective (for `n > 0`).
- How: Lifts the canonical natural-number representative `z` of `c`; shows `z` is a unit by contradiction — if not, `‖z‖<1` forces `toZModPow 1 z = 0`, contradicting that `z` is a unit mod `p` (cast of a unit via `PadicInt.zmod_cast_comp_toZModPow` and `not_isUnit_zero`).
- Hypotheses: `0 < n`.
- Uses from project: [`unitsToZModPow`, `unitsToZModPow_coe`]
- Used by: `levelMap_jointly_injective`, `augmentationIdeal_eq_span`, `exists_topological_generator`.
- Visibility: public
- Lines: 411-439 (proof: ~28 lines)
- Notes: long(30-50)? proof ~28 lines; none. Hinges on `PadicInt.ker_toZModPow`, `PadicInt.norm_le_pow_iff_mem_span_pow`, `not_isUnit_zero`.

### lemma exists_level_subset
- Type: `lemma exists_level_subset {u} {U : Set ℤ_[p]ˣ} (hU : IsOpen U) (hu : u ∈ U) : ∃ n, {v | unitsToZModPow p n v = unitsToZModPow p n u} ⊆ U`
- What: The level sets form a neighbourhood basis: any open `U` containing `u` contains some level-`n` disc around `u`.
- How: Transports `U` to `ℤ_p` via `unitsHomeo`, gets a metric ball, picks `n` with `p^{-n}` below the radius via `PadicInt.exists_pow_neg_lt`, and shows the level disc maps into the ball using `PadicInt.norm_le_pow_iff_mem_span_pow` + `ker_toZModPow`.
- Hypotheses: `U` open, `u ∈ U`.
- Uses from project: [`unitsToZModPow`, `unitsHomeo`]
- Used by: `exists_level_factorization`.
- Visibility: public
- Lines: 441-463 (proof: ~22 lines)
- Notes: none. Hinges on `unitsHomeo`, `PadicInt.exists_pow_neg_lt`, `PadicInt.ker_toZModPow`.

### lemma exists_level_factorization
- Type: `lemma exists_level_factorization (g : LocallyConstant ℤ_[p]ˣ ℤ_[p]) : ∃ N, 0 < N ∧ ∀ u v, unitsToZModPow p N u = unitsToZModPow p N v → g u = g v`
- What: Every locally constant function on `ℤ_p^×` factors through some finite level `N`.
- How: For each `u` pick a level (via `exists_level_subset`) on which `g` is constant; `IsCompact.elim_finite_subcover` extracts a finite subcover; take `N = max(t.sup nfun) 1`, then descend levels using `unitsToZModPow_le`.
- Hypotheses: `g` locally constant.
- Uses from project: [`unitsToZModPow`, `exists_level_subset`, `isClopen_unitsToZModPow_fiber`, `unitsToZModPow_le`]
- Used by: `levelMap_jointly_injective`.
- Visibility: public
- Lines: 465-488 (proof: ~23 lines)
- Notes: none. Hinges on `IsCompact.elim_finite_subcover`.

### theorem levelMap_jointly_injective
- Type: `theorem levelMap_jointly_injective (μ) (h : ∀ n, levelMap p n μ = 0) : μ = 0`
- What: The finite-level maps are jointly injective: a measure vanishing on every finite-level indicator is the zero measure.
- How: From `levelMap_eq_zero_iff` all disc-measures vanish (`hcoeff`); by `ext_locallyConstant` reduce to a locally constant `g`, factor it through level `N` (`exists_level_factorization`), write `g` as a `ℤ_p`-combination of `levelChar`s (using `unitsToZModPow_surjective` representatives), and integrate term-by-term to 0.
- Hypotheses: `levelMap p n μ = 0` for all `n`.
- Uses from project: [`PadicMeasure`, `levelMap`, `levelMap_eq_zero_iff`, `ext_locallyConstant`, `exists_level_factorization`, `unitsToZModPow`, `unitsToZModPow_surjective`, `levelChar`, `levelChar_apply_eq`, `levelChar_apply_ne`]
- Used by: `augmentationIdeal_eq_span` (`hzero`).
- Visibility: public
- Lines: 490-515 (proof: ~25 lines)
- Notes: none. Hinges on `ext_locallyConstant` + `exists_level_factorization`.

### lemma sum_levelChar_fiber
- Type: `lemma sum_levelChar_fiber {n m} (h : n ≤ m) (cbar : (ZMod (p ^ n))ˣ) : (∑ c ∈ filter(unitsMap c = cbar), levelChar p m c) = levelChar p n cbar`
- What: Refinement: the level-`m` discs sitting inside a level-`n` disc `cbar` sum to its indicator.
- How: Pointwise case split on whether `u` lies in the `cbar`-disc; in-case isolates `unitsToZModPow p m u` via `Finset.sum_eq_single`; uses `unitsToZModPow_le` to relate levels and `levelChar_apply_eq/ne`.
- Hypotheses: `n ≤ m`, `cbar` a level-`n` residue.
- Uses from project: [`levelChar`, `unitsToZModPow`, `unitsToZModPow_le`, `levelChar_apply_eq`, `levelChar_apply_ne`]
- Used by: `mapDomain_levelMap`.
- Visibility: public
- Lines: 517-537 (proof: ~19 lines)
- Notes: none

### lemma mapDomain_levelMap
- Type: `lemma mapDomain_levelMap {n m} (h : n ≤ m) (μ) : Finsupp.mapDomain (ZMod.unitsMap (pow_dvd_pow p h)) (levelMap p m μ) = levelMap p n μ`
- What: The level maps are compatible with coefficient transport along the reductions (the inverse-system maps commute with `levelMap`).
- How: Expands `levelMap m` as a sum of singles, pushes `mapDomain` through (`Finsupp.mapDomain_single`), groups fibers via `Finset.sum_fiberwise_of_maps_to`, and a `calc` collapses each fiber sum using `sum_levelChar_fiber`.
- Hypotheses: `n ≤ m`, `μ` measure.
- Uses from project: [`levelMap`, `levelChar`, `sum_levelChar_fiber`]
- Used by: `augmentationIdeal_eq_span` (`hSsub`).
- Visibility: public
- Lines: 539-567 (proof: ~28 lines)
- Notes: none. Hinges on `Finset.sum_fiberwise_of_maps_to` + `sum_levelChar_fiber`.

### lemma single_sub_one_mem_span
- Type: `lemma single_sub_one_mem_span {n} {gbar} (hg : Subgroup.zpowers gbar = ⊤) (c) : (single c 1 - 1) ∈ Ideal.span {single gbar 1 - 1}`
- What: Telescoping identity: `[c]−1` lies in the ideal generated by `[g]−1` whenever `c` is a power of the generator `g`.
- How: Writes `c = gbar^k` (`mem_powers_iff_mem_zpowers`), inducts on `k`; the successor step uses the identity `[g^{m+1}]−1 = [g]·([g^m]−1) + ([g]−1)` (proved via `single_mul_single`, `pow_succ'`, `ring`) and `Ideal.add_mem`/`mul_mem_left`.
- Hypotheses: `gbar` generates `(ZMod (p^n))ˣ`; `c` arbitrary.
- Uses from project: []
- Used by: `mem_span_of_sum_eq_zero`.
- Visibility: public
- Lines: 569-590 (proof: ~20 lines)
- Notes: none. Hinges on `MonoidAlgebra.single_mul_single`, `mem_powers_iff_mem_zpowers`.

### lemma sum_single_coeff
- Type: `lemma sum_single_coeff {n} (y : MonoidAlgebra ℤ_[p] (ZMod (p ^ n))ˣ) : (∑ c, single c (y c)) = y := Finsupp.univ_sum_single y`
- What: Reconstruction: a group-ring element equals the sum of its single components.
- How: Direct `Finsupp.univ_sum_single`.
- Hypotheses: `y` a group-ring element.
- Uses from project: []
- Used by: `mem_span_of_sum_eq_zero`, `augmentationIdeal_eq_span` (`hlev`).
- Visibility: public
- Lines: 592-595 (term)
- Notes: none

### lemma mem_span_of_sum_eq_zero
- Type: `lemma mem_span_of_sum_eq_zero {n} {gbar} (hg : Subgroup.zpowers gbar = ⊤) (x) (hx : ∑ c, x c = 0) : x ∈ Ideal.span {single gbar 1 - 1}`
- What: An augmentation-trivial group-ring element (coefficient sum 0) lies in the ideal generated by `[g]−1`, `g` a generator.
- How: Decomposes `x = ∑ x(c)·([c]−1) + (∑ x(c))·1` via `sum_single_coeff`; the second term vanishes by `hx`; each `x(c)·([c]−1) ∈ span` by `single_sub_one_mem_span` + `Algebra.smul_def`/`Ideal.mul_mem_left`; `Ideal.sum_mem`.
- Hypotheses: `gbar` generates; `x` has zero coefficient sum.
- Uses from project: [`sum_single_coeff`, `single_sub_one_mem_span`]
- Used by: `augmentationIdeal_eq_span` (`hSne`).
- Visibility: public
- Lines: 597-626 (proof: ~28 lines)
- Notes: none. Hinges on `single_sub_one_mem_span`, `sum_single_coeff`, `Algebra.smul_def`.

### lemma sum_levelMap_coeff
- Type: `lemma sum_levelMap_coeff (n) (E) : ∑ c, (levelMap p n E) c = deg p E`
- What: The coefficient sum of `levelMap n E` equals the degree (augmentation) of `E`.
- How: `levelMap_apply_coeff` per coefficient, then `map_sum E` and `sum_levelChar` collapse `∑ levelChar = 1`.
- Hypotheses: `n : ℕ`, `E` measure.
- Uses from project: [`levelMap`, `levelMap_apply_coeff`, `deg`, `sum_levelChar`, `levelChar`]
- Used by: `augmentationIdeal_eq_span` (`hSne`).
- Visibility: public
- Lines: 628-633 (proof: ~3 lines)
- Notes: none

### lemma dirac_sub_one_mul_apply
- Type: `lemma dirac_sub_one_mul_apply (a) (ν) (f) : ((dirac p a - 1) * ν) f = ν ((f.comp (unitsMulCM₂ p)).curry a) - ν ((f.comp (unitsMulCM₂ p)).curry 1)`
- What: Evaluation of `([a]−[1])·ν` is the translation difference `∫ f(a·−) dν − ∫ f(−) dν`.
- How: Unfolds the product through `LinearMap.sub_apply`, `dirac_apply`, `units_one_def`, and `innerInt_apply` (twice).
- Hypotheses: `a ∈ ℤ_p^×`, `ν` measure, `f` test function.
- Uses from project: [`PadicMeasure`, `dirac`, `dirac_apply`, `units_one_def`, `innerInt`, `innerInt_apply`, `unitsMulCM₂`]
- Used by: `augmentationIdeal_eq_span` (`hSmem`).
- Visibility: public
- Lines: 635-643 (proof: ~4 lines)
- Notes: none

### def unitsPowCM
- Type: `def unitsPowCM (k : ℕ) : C(ℤ_[p]ˣ, ℤ_[p]) := ⟨fun u => (u : ℤ_[p]) ^ k, ...⟩`
- What: The power-moment function `x ↦ x^k` on `ℤ_p^×` as a continuous map into `ℤ_p`.
- How: Bundles `u ↦ u^k` with continuity from `Units.continuous_val.pow k`.
- Hypotheses: `k : ℕ`.
- Uses from project: []
- Used by: `eq_zero_of_forall_unitsPowCM_eq_zero`, `units_mul_apply_unitsPowCM`, `mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero`, `dirac_sub_one_mem_nonZeroDivisors`, `pseudoMeasure_eq_zero_of_moments`.
- Visibility: public
- Lines: 650-651 (def)
- Notes: none

### theorem eq_zero_of_forall_unitsPowCM_eq_zero
- Type: `theorem eq_zero_of_forall_unitsPowCM_eq_zero (μ) (h : ∀ k, 0 < k → μ (unitsPowCM p k) = 0) : μ = 0`
- What: **RJW Lem. 3.36(i)** — a measure on `ℤ_p^×` whose power moments `∫ x^k` all vanish (`k>0`) is zero.
- How: Step 1: positive Mahler coefficients of `ι μ` vanish — relates `descPochhammer` (which has no constant term, `X ∣ descPochhammer`) to `unitsPowCM`, integrates termwise to 0, divides by `n!` (`nsmul_right_injective`). Step 2: `mahlerTransform_injective` forces `ι μ = c₀ • δ₀`. Step 3: `ψ` kills `ι μ` (`isSupportedOn_units_iff_psi_eq_zero` + `res_iota`) but fixes multiples of `δ₀` (computing `shiftDiv p 0 = 0`), forcing `c₀ = 0`; conclude via `iota_injective`.
- Hypotheses: `μ (unitsPowCM p k) = 0` for all `k > 0`.
- Uses from project: [`PadicMeasure`, `iota`, `mahler`-API (`mahler_apply`), `unitsPowCM`, `unitsValCM`, `mahlerTransform_injective`, `coeff_mahlerTransform`, `dirac`, `dirac_apply`, `psi`, `isSupportedOn_units_iff_psi_eq_zero`, `res_iota`, `shiftDiv`, `digit`, `isClopen_pZp`, `iota_injective`]
- Used by: `mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero`, `pseudoMeasure_eq_zero_of_moments`.
- Visibility: public
- Lines: 657-744 (proof: ~87 lines)
- Notes: OVER-50 (needs /decompose-proof). Three labelled steps. Hinges on `mahlerTransform_injective`, `Ring.descPochhammer_eq_factorial_smul_choose`, `isSupportedOn_units_iff_psi_eq_zero`, `iota_injective`.

### lemma units_mul_apply_unitsPowCM
- Type: `lemma units_mul_apply_unitsPowCM (μ ν) (k) : (μ * ν) (unitsPowCM p k) = μ (unitsPowCM p k) * ν (unitsPowCM p k)`
- What: Power moments are multiplicative for convolution: `∫(xy)^k d(μ⋆ν) = (∫x^k dμ)(∫y^k dν)`.
- How: Unfolds via `units_mul_apply`; a `curry` computation shows the inner integral of `(xy)^k` is `(ν(unitsPowCM k))·unitsPowCM k`, using `mul_pow`; then `map_smul`.
- Hypotheses: `μ, ν` measures; `k : ℕ`.
- Uses from project: [`PadicMeasure`, `units_mul_apply`, `innerInt`, `innerInt_apply`, `unitsPowCM`, `unitsMulCM₂`]
- Used by: `mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero`.
- Visibility: public
- Lines: 746-766 (proof: ~19 lines)
- Notes: none

### theorem mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero
- Type: `theorem mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero (μ) (h : ∀ k, 0 < k → μ (unitsPowCM p k) ≠ 0) : μ ∈ nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ)`
- What: **RJW Lem. 3.36(ii)** — a measure with all power moments `∫ x^k ≠ 0` (`k>0`) is a non-zero-divisor.
- How: For `ν*μ=0`, evaluates at `unitsPowCM k` via `units_mul_apply_unitsPowCM`; `mul_eq_zero` + the nonvanishing hypothesis forces `ν(unitsPowCM k)=0`, so `ν=0` by `eq_zero_of_forall_unitsPowCM_eq_zero`; both sides via `mem_nonZeroDivisors_iff` and `mul_comm`.
- Hypotheses: `μ (unitsPowCM p k) ≠ 0` for all `k > 0`.
- Uses from project: [`PadicMeasure`, `unitsPowCM`, `eq_zero_of_forall_unitsPowCM_eq_zero`, `units_mul_apply_unitsPowCM`]
- Used by: `dirac_sub_one_mem_nonZeroDivisors`.
- Visibility: public
- Lines: 768-782 (proof: ~10 lines)
- Notes: none

### theorem dirac_sub_one_mem_nonZeroDivisors
- Type: `theorem dirac_sub_one_mem_nonZeroDivisors {a} (ha : ∀ k, 0 < k → (a : ℤ_[p]) ^ k ≠ 1) : (dirac p a - 1) ∈ nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ)`
- What: `[a]−[1]` is a non-zero-divisor when `a` has no torsion moments (`a^k ≠ 1`).
- How: Reduces to `mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero`; computes the `k`-th moment of `[a]−[1]` to be `a^k − 1` (via `dirac_apply`, `units_one_def`), nonzero by `ha` and `sub_ne_zero`.
- Hypotheses: `a^k ≠ 1` for all `k > 0`.
- Uses from project: [`PadicMeasure`, `dirac`, `dirac_apply`, `units_one_def`, `unitsPowCM`, `mem_nonZeroDivisors_of_forall_unitsPowCM_ne_zero`]
- Used by: `pseudoMeasure_eq_zero_of_moments`, `dirac_sub_one_mem_nonZeroDivisors'`.
- Visibility: public
- Lines: 786-798 (proof: ~7 lines)
- Notes: none

### abbrev QuotientField
- Type: `noncomputable abbrev QuotientField := FractionRing (PadicMeasure p ℤ_[p]ˣ)`
- What: The total ring of fractions `Q(ℤ_p^×)` of the Iwasawa algebra (RJW Def. 3.34).
- How: `FractionRing` of the measure ring.
- Hypotheses: none beyond `p` prime.
- Uses from project: [`PadicMeasure`]
- Used by: `IsPseudoMeasure`, `isPseudoMeasure_algebraMap`, `pseudoMeasure_eq_zero_of_moments`, `isPseudoMeasure_mk'`, `isPseudoMeasure_iff_exists`.
- Visibility: public
- Lines: 804-805 (abbrev)
- Notes: none

### def IsPseudoMeasure
- Type: `def IsPseudoMeasure (q : QuotientField p) : Prop := ∀ g : ℤ_[p]ˣ, ∃ ν, algebraMap _ (QuotientField p) (dirac p g - 1) * q = algebraMap _ _ ν`
- What: A pseudo-measure is an element `q ∈ Q(ℤ_p^×)` with `([g]−[1])·q ∈ Λ(ℤ_p^×)` (image of a measure) for every `g` (RJW Def. 3.34).
- How: Existential predicate over witnessing measures `ν`.
- Hypotheses: `q ∈ QuotientField p`.
- Uses from project: [`QuotientField`, `PadicMeasure`, `dirac`]
- Used by: `isPseudoMeasure_algebraMap`, `pseudoMeasure_eq_zero_of_moments`, `isPseudoMeasure_mk'`, `isPseudoMeasure_iff_exists`.
- Visibility: public
- Lines: 811-813 (def)
- Notes: none

### theorem isPseudoMeasure_algebraMap
- Type: `theorem isPseudoMeasure_algebraMap (μ) : IsPseudoMeasure p (algebraMap _ _ μ)`
- What: Every measure (its image in `Q`) is a pseudo-measure.
- How: Witness `ν := (dirac p g − 1) * μ`; `map_mul`.
- Hypotheses: `μ` measure.
- Uses from project: [`IsPseudoMeasure`, `PadicMeasure`, `dirac`]
- Used by: unused in file
- Visibility: public
- Lines: 816-818 (proof: term, ~2 lines)
- Notes: none

### theorem pseudoMeasure_eq_zero_of_moments
- Type: `theorem pseudoMeasure_eq_zero_of_moments {a} (ha : ∀ k, 0<k → a^k ≠ 1) (q) (hq : IsPseudoMeasure p q) (h : ∀ k, 0<k → ∀ ν, (([a]−1)q = ν) → ν (unitsPowCM p k) = 0) : q = 0`
- What: **RJW Lem. 3.36(iii)** — a pseudo-measure all of whose moments (`k>0`) vanish is zero.
- How: Take the witness `ν₀` for `g=a`; it is 0 by `eq_zero_of_forall_unitsPowCM_eq_zero`; since `[a]−1` is a non-zero-divisor (`dirac_sub_one_mem_nonZeroDivisors`) its image is a unit (`IsLocalization.map_units`), and `q = u⁻¹·(u·q) = u⁻¹·0 = 0`.
- Hypotheses: `a^k ≠ 1` (`k>0`); `q` a pseudo-measure; all witnessed moments vanish.
- Uses from project: [`QuotientField`, `IsPseudoMeasure`, `PadicMeasure`, `dirac`, `unitsPowCM`, `eq_zero_of_forall_unitsPowCM_eq_zero`, `dirac_sub_one_mem_nonZeroDivisors`]
- Used by: unused in file
- Visibility: public
- Lines: 824-841 (proof: ~12 lines)
- Notes: none. Hinges on `IsLocalization.map_units`.

### theorem exists_topological_generator
- Type: `theorem exists_topological_generator (hp2 : p ≠ 2) : ∃ a : ℤ_[p]ˣ, ∀ n, Subgroup.zpowers (unitsToZModPow p n a) = ⊤`
- What: For odd `p`, `ℤ_p^×` has a topological generator `a` whose image generates `(ℤ/p^n)^×` for every `n` (RJW Lem. 3.38).
- How: The per-level generator sets `t n` are nested (`unitsToZModPow_le` + `ZMod.unitsMap_surjective`), nonempty (cyclicity `ZMod.isCyclic_units_of_prime_pow` for `n>0`; subsingleton for `n=0`), and closed (finite union of clopen fibers); a point of `⋂ t n` (compactness, `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`) is a generator.
- Hypotheses: `p ≠ 2` (essential: `(ZMod 8)ˣ` not cyclic).
- Uses from project: [`unitsToZModPow`, `unitsToZModPow_le`, `unitsToZModPow_surjective`, `isClopen_unitsToZModPow_fiber`]
- Used by: unused in file (downstream consumers elsewhere).
- Visibility: public
- Lines: 852-889 (proof: ~37 lines)
- Notes: long(30-50) (37 lines). Hinges on `ZMod.isCyclic_units_of_prime_pow`, `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`, `ZMod.unitsMap_surjective`.

### theorem augmentationIdeal_eq_span
- Type: `theorem augmentationIdeal_eq_span {a} (ha : ∀ n, Subgroup.zpowers (unitsToZModPow p n a) = ⊤) : augmentationIdeal p = Ideal.span {dirac p a - 1}`
- What: **RJW Lem. 3.38** — for a topological generator `a` the augmentation ideal is the principal ideal `([a]−[1])`.
- How: `le_antisymm`. Hard direction (⊆): a weak-topology compactness argument. Builds closed sets `K` (linearity constraints) and `S n` (functionals matching `μ` at level `n` via `dirac_sub_one_mul_apply`); `hSmem` relates membership to `levelMap (([a]−1)ν − μ) = 0`; `hSsub` (nesting) uses `mapDomain_levelMap`; `hSne` (nonempty) uses `mem_span_of_sum_eq_zero` + `sum_levelMap_coeff` to build the witness `ν` at each level; a point of `⋂ S n` (compactness) gives a measure `ν` with `(([a]−1)ν − μ) = 0` by `levelMap_jointly_injective`. Easy direction (⊇): `deg (dirac a) = 1`.
- Hypotheses: `a` a topological generator.
- Uses from project: [`augmentationIdeal`, `unitsToZModPow`, `dirac`, `levelChar`, `unitsMulCM₂`, `levelMap`, `levelMap_eq_zero_iff`, `levelMap_jointly_injective`, `dirac_sub_one_mul_apply`, `mapDomain_levelMap`, `mem_span_of_sum_eq_zero`, `sum_levelMap_coeff`, `sum_levelChar`, `sum_single_coeff`, `levelMap_smul`, `levelMap_dirac`, `unitsToZModPow_surjective`, `deg`, `PadicMeasure`]
- Used by: `isPseudoMeasure_mk'`.
- Visibility: public
- Lines: 895-1007 (proof: ~112 lines)
- Notes: OVER-50 (needs /decompose-proof). Largest proof in file. Hinges on `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`, `levelMap_jointly_injective`, `mem_span_of_sum_eq_zero`, `mapDomain_levelMap`.

### theorem isPseudoMeasure_mk'
- Type: `theorem isPseudoMeasure_mk' {a} (ha : ∀ n, zpowers (unitsToZModPow p n a) = ⊤) (hreg : (dirac p a - 1) ∈ nonZeroDivisors ...) (μ) : IsPseudoMeasure p (IsLocalization.mk' (QuotientField p) μ ⟨_, hreg⟩)`
- What: **RJW Lem. 3.38** — for a topological generator `a` and any measure `μ`, the quotient `μ/([a]−[1])` is a pseudo-measure.
- How: For each `g`, `[g]−1 ∈ augmentationIdeal = span{[a]−1}` (`augmentationIdeal_eq_span`), so `[g]−1 = ([a]−1)·ν`; witness `ν*μ`, then rearrange the `algebraMap` product using `IsLocalization.mk'_spec'`.
- Hypotheses: `a` topological generator; `[a]−1` a non-zero-divisor; `μ` measure.
- Uses from project: [`IsPseudoMeasure`, `QuotientField`, `PadicMeasure`, `dirac`, `unitsToZModPow`, `augmentationIdeal`, `augmentationIdeal_eq_span`, `deg`]
- Used by: `isPseudoMeasure_iff_exists`.
- Visibility: public
- Lines: 1011-1029 (proof: ~18 lines)
- Notes: none. Hinges on `augmentationIdeal_eq_span`, `IsLocalization.mk'_spec'`.

### theorem dirac_sub_one_mem_nonZeroDivisors'
- Type: `theorem dirac_sub_one_mem_nonZeroDivisors' {a} (ha : ∀ k, 0<k → a^k ≠ 1) : (dirac p a - 1) ∈ nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ) := dirac_sub_one_mem_nonZeroDivisors p ha`
- What: `[a]−[1]` is a non-zero-divisor for a topological generator `a` (restatement convenience).
- How: Direct delegation to `dirac_sub_one_mem_nonZeroDivisors`.
- Hypotheses: `a^k ≠ 1` for all `k>0`.
- Uses from project: [`PadicMeasure`, `dirac`, `dirac_sub_one_mem_nonZeroDivisors`]
- Used by: unused in file
- Visibility: public
- Lines: 1034-1038 (term)
- Notes: none

### theorem isPseudoMeasure_iff_exists
- Type: `theorem isPseudoMeasure_iff_exists {a} (ha : ∀ n, zpowers (unitsToZModPow p n a) = ⊤) (hreg : (dirac p a - 1) ∈ nonZeroDivisors ...) (q) : IsPseudoMeasure p q ↔ ∃ μ, q = IsLocalization.mk' (QuotientField p) μ ⟨_, hreg⟩`
- What: Every pseudo-measure has the shape `μ/([a]−[1])`, and conversely (RJW: "all pseudo-measures have this shape").
- How: (→) take witness `ν` for `g=a` and rewrite via `IsLocalization.eq_mk'_iff_mul_eq` + `mul_comm`. (←) `isPseudoMeasure_mk'`.
- Hypotheses: `a` topological generator; `[a]−1` a non-zero-divisor.
- Uses from project: [`IsPseudoMeasure`, `QuotientField`, `PadicMeasure`, `dirac`, `unitsToZModPow`, `isPseudoMeasure_mk'`]
- Used by: unused in file
- Visibility: public
- Lines: 1042-1057 (proof: ~7 lines)
- Notes: none. Hinges on `IsLocalization.eq_mk'_iff_mul_eq`.

---

## File Summary

**Total declarations: 47** — defs/abbrevs: 12 (`mulCM₂`, `conv`, `deg`, `augmentationIdeal`, `unitsMulCM₂`, `unitsConv`, `unitsToZModPow`, `levelChar`, `levelMap`, `unitsPowCM`, `QuotientField`, `IsPseudoMeasure`); lemmas+theorems: 31; instances: 4 (`Mul`, `One`, `CommRing`, plus the two instance-like `Mul`/`One` — count = `Mul`, `One`, `CommRing`).

Precisely: 12 defs/abbrevs, 31 lemmas/theorems, 4 instances (`Mul`, `One`, `CommRing` — three; the file has exactly three `instance` keywords).

**Key API (used by ≥3 in file):**
- `unitsToZModPow` — foundational reduction map; used by ~12 decls.
- `levelChar` (+ `levelChar_apply_eq`, `levelChar_apply_ne`) — level indicators; used by ~10 decls each.
- `levelMap` — finite-level ring map; used by ~8 decls.
- `dirac` (project), `PadicMeasure`, `innerInt` — pervasive.
- `unitsToZModPow_le`, `unitsToZModPow_surjective`, `unitsMulCM₂`, `sum_single_coeff` — each used by ≥3.
- `eq_zero_of_forall_unitsPowCM_eq_zero` — used by 2 (Lem 3.36(ii),(iii)); `dirac_sub_one_mem_nonZeroDivisors` — used by 2.

**Unused in file (leaf API for downstream projects):** `conv_mul_def`, `conv_mul_apply`, `conv_one_def`, `units_mul_def`, `units_dirac_mul_dirac`, `isPseudoMeasure_algebraMap`, `pseudoMeasure_eq_zero_of_moments`, `exists_topological_generator`, `dirac_sub_one_mem_nonZeroDivisors'`, `isPseudoMeasure_iff_exists`. (These are the public-facing theorems; consumers are `ZetaP`, `EisensteinFamily`, etc. per file docstrings.)

**Declarations with `sorry`: NONE.**

**`set_option`: NONE.** **`TODO`: NONE.**

**Proofs > 50 lines (OVER-50, need /decompose-proof): 4**
1. `augmentationIdeal_eq_span` — ~112 lines (1107-1007).
2. `levelMap` (`map_mul'` field) — ~89 lines total / ~67 for `map_mul'` (262-351).
3. `eq_zero_of_forall_unitsPowCM_eq_zero` — ~87 lines (657-744).
4. `CommRing` instance — ~55 lines aggregate record (81-135).

**Proofs 30-50 lines (long): 1**
1. `exists_topological_generator` — ~37 lines (852-889).
(`unitsToZModPow_surjective` ~28, `mapDomain_levelMap` ~28, `mem_span_of_sum_eq_zero` ~28, `levelMap_jointly_injective` ~25, `exists_level_factorization` ~23, `exists_level_subset` ~22 are all just under 30.)

**Other notes:** whole file is `noncomputable`; the `convolution`/`degree` sections are stated for a general compact commutative topological monoid `G` (generalised in the §11 R11.5 pass), with `ℤ_p^×`-named specialisations preserving the downstream API verbatim. `p ≠ 2` enters only at `exists_topological_generator` (needs `(ℤ/p^n)^×` cyclic).
