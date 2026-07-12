<!-- Adversarial /develop --decompose attack log, agent a84d3e4e721fd839c, archived 2026-07-06 -->

All verification complete. Compiling the adversarial report.

---

# ADVERSARIAL VERIFICATION REPORT — EllipticCurve/{WeierstrassModel,Basic,GroupLaw,Torsion}.lean + GroupScheme/MuN.lean

**Method note.** No file edited, no `lake build` run. Statement-level attacks executed against the sources quoted in `.mathlib-quality/{plan,decomposition,decomposition-km1,decomposition-gme2}.md`; discharge attacks executed by `lean_local_search` + direct reads of the pinned mathlib source in `.lake/packages/mathlib`. Elaboration facts are secured by build artifacts: all five audited files have `.olean`s newer than their sources (post-expert-review revisions of `Basic.lean`/`GroupLaw.lean` included), so name-resolution/letI claims below are grounded, not guessed. Audited files (absolute): `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves/projects/ModularCurves/ModularCurves/EllipticCurve/{WeierstrassModel,Basic,GroupLaw,Torsion}.lean`, `.../GroupScheme/MuN.lean`.

**Discharge-attack ledger (category [5], shared by the blocks below).** All cited names verified present in the pinned mathlib, with the load-bearing content checked at source:
- `CategoryTheory.Over.grpObjMkPullbackSnd` — `Monoidal/Cartesian/Over.lean:317`: `[GrpObj (Over.mk f)] : GrpObj (Over.mk (pullback.snd f g))`, `f : R ⟶ X`, `g : S ⟶ X`. **Orientation: group structure on the mk of the FIRST leg, output on `pullback.snd f g` — exactly the `baseChange` usage.** Bonus finds: `isCommMonObj_mk_pullbackSnd` (line 311) and simp lemma `monObjMkPullbackSnd_one` (line 322) discharge `baseChange.comm`/`one_eq_zero`.
- `CategoryTheory.Hom.monoid/group/commGroup` — `Cartesian/Mon.lean:209`, `Grp.lean:59,306`: `mul f₁ f₂ := lift f₁ f₂ ≫ μ`, `inv f := f ≫ ι`. **Pointwise (convolution) structure, NOT `End`-composition**; `Hom.commGroup` needs `[IsCommMonObj G]` + braided (provided by the files' local instances).
- `CategoryTheory.GrpObj.comp_zpow` — `Grp.lean:177`: `f ≫ g ^ n = (f ≫ g) ^ n` for `n : ℤ` — exactly the `point_smul_eq_comp_mulBy` engine.
- `AlgebraicGeometry.Scheme.Hom.finrank` — `Morphisms/FlatRank.lean:88`: `(f : X ⟶ S) (s : S) : ℕ`, **no instance arguments at all**; plus `finrank_pullback_snd`, `isLocallyConstant_finrank`.
- `Module.free_of_flat_of_isLocalRing` (`RingTheory/LocalRing/Module.lean:302`), `AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite` (`ZariskisMainTheorem.lean:371`, hypotheses `[IsProper f] [LocallyQuasiFinite f]`), `Scheme.GlueData` (`Gluing.lean`), `smoothOfRelativeDimension_isStableUnderBaseChange` (`Morphisms/Smooth.lean:166`), `Equiv.addCommGroup` (to_additive of `Equiv.commGroup`, `Algebra/Group/TransferInstance.lean:173`, transports target→source ✓), `Additive.ofMul` (`TypeTags/Basic.lean:51`), `Algebra.norm` (`Norm/Defs.lean:61`), `IsCommMonObj (X) [MonObj X]` (`Monoidal/Mon.lean:1213`), `class GrpObj extends MonObj` (`Monoidal/Grp.lean:43`), `instance : HasTerminal Scheme` (`AlgebraicGeometry/Limits.lean:59`), `Scheme.Hom.fiber = pullback f (Y.fromSpecResidueField y)` / `fiberι = fst` / `fiberToSpecResidueField = snd` (`Fiber.lean:37–48`), `class Etale` (`Morphisms/Etale.lean:41`), `class Flat` (`Morphisms/Flat.lean:42`), `HasColimitsOfShape (Discrete σ) Scheme [Small.{u} σ]` (`Limits.lean:187`), `WeierstrassCurve.baseChange` (`Weierstrass.lean:236`), `WeierstrassCurve.IsElliptic` (`Weierstrass.lean:359`), `Over.cartesianMonoidalCategory` with **tensor unit `Over.mk (𝟙 X)`** (`Cartesian/Over.lean:34`). One negative find, load-bearing below: `WeierstrassCurve.Affine.Point` (`Affine/Point.lean:467`) is `zero | some (x y) (h : W.Nonsingular x y)` — **nonsingular points only**.

---

## WeierstrassModel.lean

### `SpecPoints` (WeierstrassModel.lean:45)
- Attacks: [3] No `Field K` demanded — deliberately general; `Algebra R K` is the only bridge, and `Spec.map (ofHom (algebraMap R K)) : Spec K ⟶ Spec R` orientation is correct. → clean
- Attacks: [2] `K = 0` (zero ring): `Spec 0 = ∅`, subtype collapses to a singleton (unique `∅ ⟶ X`, condition trivially satisfied) — harmless junk value, never consumed (interface uses fields only). → survives
- Attacks: [1] Definition = `Hom_{Spec R}(Spec K, X)` — standard K-points; no contradicting mathlib formulation found (mathlib has no scheme-valued-points-over-base def to clash with). → survives
- Verdict: SURVIVED

### `IsWeierstrassModel` (WeierstrassModel.lean:59)
- Attacks: [4] Docstring (and A2 in decomposition.md) promise the K-point identification "**naturally in K and sending x₀ to 0**"; the Lean field is `points : Nonempty (SpecPoints X f K ≃ …)` — an *unnatural, unpointed, mere-cardinality* bijection, one per K, with no compatibility. Both promised clauses were dropped in formalisation. → **drift, load-bearing**
- Attacks: [1] Comparison type `(W.baseChange K).toAffine.Point` contains **only nonsingular** affine points (`some` carries `Nonsingular`, verified at `Affine/Point.lean:467`) + `zero`; the honest projective cubic's K-points include singular points. For singular `W` the documented model cannot satisfy the spec (counterexample under `projModel_isWeierstrassModel`). → spec/type mismatch for non-elliptic `W`
- Attacks: [3] No smoothness/flatness/reducedness field: `Nonempty(≃)` on field-points cannot see nilpotents, so the interface cannot separate a model from its thickenings (exploited below to kill uniqueness). Docstring even says "plus properness and **smoothness** pins the model down" — smoothness is nowhere in the structure. → missing hypothesis
- Attacks: [2] `R = 0`: `Spec 0 = ∅`, all fields vacuous/trivially satisfiable — consistent. → survives edges
- Verdict: NEEDS-FIX(upgrade `points` to a natural-in-K, pointed equivalence (x₀ ↦ `.zero`), and either restrict the points clause to `[W.IsElliptic]` or add a geometric field (smoothness over the elliptic locus / flatness+reducedness), else `isWeierstrassModel_unique` is unrecoverable)

### `projModel` (WeierstrassModel.lean:74) — DS1, sorriness not at issue
- Attacks: [4] Docstring fixes construction "gluing the affine charts z=1, y=1 (KM 2.2)" but decomposition-gme2 A7.e **adopts Hida's Proj-of-one-graded-ring route instead** ("This replaces the glue-two-charts plan of T-A2 … adopt Hida's route") — the file docstring and the binding worker plan now disagree on T-A2's route. → doc drift, fix docstring
- Attacks: [5] Both discharge targets exist: `Scheme.GlueData` ✓ and `AlgebraicGeometry.Proj` route per gme2 ✓. → dischargeable
- Attacks: [3] Signature `(W : WeierstrassCurve R) : Scheme.{u}` — no `IsElliptic`, correct: the model exists for all W (KM 2.2 works with any Weierstrass equation). → right generality
- Verdict: SURVIVED (as data slot; its *specification* defects are charged to `IsWeierstrassModel`/`projModel_isWeierstrassModel`)

### `projModelπ` (WeierstrassModel.lean:77)
- Attacks: [3] Target `Spec (.of R)` matches `SpecPoints`/`IsWeierstrassModel` plumbing; no extra hypotheses. → clean
- Attacks: [4] "structure morphism to Spec R" — matches KM 2.2/Loeffler §3.3 display (model over S). → faithful
- Attacks: [2] R = 0: morphism into empty scheme forces empty model — consistent with V(cubic) ⊆ ℙ²_0 = ∅. → survives
- Verdict: SURVIVED

### `projModelZero` (WeierstrassModel.lean:80)
- Attacks: [4] "[0:1:0]" section matches Loeffler Def 3.3.3/KM 2.2 base point; on the cubic `Y²Z + … = X³ + …` the plane point [0:1:0] always lies on the curve (Z=0 ⟹ X³=0), for every W — so a section exists for all W, spec shape is satisfiable. → faithful
- Attacks: [3] Constrained by `IsWeierstrassModel.section_comp` only through the spec theorem; pointedness of the *points* bijection was dropped (see `IsWeierstrassModel`), so DS1's zero is under-pinned until that fix. → inherits spec gap
- Attacks: [2] N/A base cases (any R fine, zero ring degenerates consistently). → survives
- Verdict: SURVIVED (under-pinned pending the `IsWeierstrassModel.points` fix)

### `projModel_isWeierstrassModel` (WeierstrassModel.lean:84)
- Attacks: [1] **Counterexample for singular W.** `R = K = 𝔽₅`, `W : y² = x³` (all aᵢ = 0). Honest projective model `V(Y²Z − X³)`: affine points biject with t ↦ (t², t³) (5 points, including the cusp) + [0:1:0] ⟹ **6** rational points. `(W.baseChange 𝔽₅).toAffine.Point` = `zero` + nonsingular affine = 1 + 4 = **5** elements. No bijection ⟹ `points` fails for the documented model. The theorem (quantified over *all* W) is inconsistent with DS1's registered construction. → REJECTED for singular W
- Attacks: [4] Sources cited (KM 2.2, Loeffler 3.3.3) state the model *display*, not this point-comparison; the singular-case clash is an artifact of comparing against mathlib's nonsingular-only `Point` type — a formalisation choice not present in any quoted source. → drift
- Attacks: [2] For `[W.IsElliptic]` every K-point of the cubic is nonsingular, bijection holds classically — restriction fixes it. Also N/A: `R = 0` vacuous. → fix identified
- Verdict: REJECTED(false as stated for singular W against the registered projModel — 𝔽₅ cuspidal count 6 ≠ 5; fix: require `[W.IsElliptic]` here (and in the `points` clause), or compare against a point type that includes singular points)

### `projModel_smooth` (WeierstrassModel.lean:91)
- Attacks: [4] Loeffler Def 3.3.3 verbatim in decomposition A3 ("If Δ(α,β) ∈ Γ(S,O_S)ˣ, this is an elliptic curve over S") — statement direction matches (unit disc ⟹ smooth rel dim 1). Module docstring (line 17) promises "smooth … **iff** Δ(W) is a unit"; converse nowhere stated — coverage gap only, not drift in this decl. → faithful, note iff-gap
- Attacks: [2] char 2/3: mathlib `Δ` has the universal a₁…a₆ formula, Silverman III.1.4(a) holds in all characteristics; `R = 0`: `IsElliptic` holds (0 is a unit), model empty, smoothness vacuous. → survives
- Attacks: [5] `SmoothOfRelativeDimension` class exists (`Morphisms/Smooth.lean`), and gme2 A7.e transcribes Hida's chartwise Jacobian proof (p. 114) — dischargeable. → verified
- Verdict: SURVIVED

### `isWeierstrassModel_unique` (WeierstrassModel.lean:97)
- Attacks: [1] **Thickening counterexample (unconditional, even for elliptic W).** R = ℚ, W elliptic, F the homogeneous cubic. X = V(F), X′ = V(F²) ⊆ ℙ²_ℚ: X′ is proper, lfp; (F²) ⊆ (F) makes V(F) a closed subscheme of V(F²), so x₀ lifts to a section of X′; `Spec K` is reduced so every K-point of X′ factors uniquely through X′_red = V(F) (F irreducible ⟹ radical), giving `SpecPoints X′ K ≃ SpecPoints X K ≃ Point` for every field K. Both tuples satisfy `IsWeierstrassModel W`, but V(F) is reduced and V(F²) is not (F ≠ 0, F² = 0 in O_{X′}), so no isomorphism `e : X ≅ X′` exists. → FALSE as stated
- Attacks: [3] Root cause: interface has no smoothness/reducedness and `points` is unnatural/unpointed — note that even upgrading `points` to a *natural pointed* field-point equivalence does NOT exclude thickenings (reduction-factorisation is natural and pointed); a geometric hypothesis is mandatory. → hypothesis to add
- Attacks: [4] KM 2.2.5 (cited) is uniqueness for models of an *elliptic curve* — i.e., among smooth pointed models; the Lean statement quantifies over arbitrary `IsWeierstrassModel` witnesses, strictly stronger than the source. Also: quote itself is PENDING-SOURCE(KM) per decomposition A4 ("Hida GME to be mined as substitute quote"). → strengthening + quote gap
- Verdict: REJECTED(V(F) vs V(F²) over ℚ; fix: assume `[W.IsElliptic]` plus `SmoothOfRelativeDimension 1 f` and `… f′` (or bake smoothness-when-elliptic into the structure), matching KM 2.2.5's actual scope) — also QUOTE-MISSING

---

## Basic.lean

### `sectionFiberPoint` (Basic.lean:45)
- Attacks: [5] Orientation vs mathlib `Fiber.lean`: `fiber f y = pullback f (fromSpecResidueField y)` with `fst → X`, `snd → Spec κ(y)`; `pullback.lift (fromSpec ≫ z) (𝟙 _)` puts the E-leg first and the κ(s)-leg second — correct; condition discharged by `hz`. → verified at mathlib source
- Attacks: [2] Works at non-closed points s (generic points included) — κ(s) = function field; construction is uniform. `S = ∅`: no s, vacuous. → survives
- Attacks: [1] Is it *the* canonical fibre point of the section? Composing with `fiberι` returns `fromSpec ≫ z` and with `fiberToSpecResidueField` returns `𝟙` — the unique such lift by pullback universality. → pinned
- Verdict: SURVIVED

### `FibrewiseElliptic` (Basic.lean:57)
- Attacks: [seed/1] Pointedness clause orientation: `sectionFiberPoint π z hz s ≫ e.hom = projModelZero W` — LHS: `Spec κ(s) ⟶ fiber ⟶ projModel W`, RHS: `Spec (.of κ(s)) ⟶ projModel W`; sources and targets agree (CommRingCat.of ∘ coe is defeq-identity on `residueField`, confirmed by fresh olean). Direction (fibre-point pushed forward along `e.hom`, compared to model's zero) is the correct pointedness equation; first clause `e.hom ≫ projModelπ W = π.fiberToSpecResidueField s` correctly matches structure maps to Spec κ(s) (both are `pullback.snd`-style). → correct as seeded
- Attacks: [seed/4] `∀ s : S` ranges over **all** scheme-theoretic points (CoeSort to the carrier), not just closed points — faithful to Loeffler "all fibres" / EGA usage; over a field-with-one-point and over generic points alike. → faithful
- Attacks: [1] Bridge-form adequacy over imperfect residue fields: the fibre has a rational point (the section's fibre point), and Silverman III.3.1/BB-RR works over any field given a rational point, so pointed-Weierstrass-iso ⟺ smooth proper geom-connected genus 1 holds for every κ(s), imperfect included; `W.IsElliptic` conjunct prevents nodal/cuspidal fibres. → no counterexample found
- Attacks: [3] Governance: WeierstrassModel.lean lines 24–25 forbid downstream use of `projModel` "except through `IsWeierstrassModel` and the theorems stated here", yet this definition references `projModel/projModelπ/projModelZero` raw (sanctioned by expert review Q2, but the consumption rule text was never amended). Meaning of the definition is parasitic on DS1 + the (defective) `IsWeierstrassModel` spec until T-A2/T-A4 land fixed. → consistency nit
- Verdict: SURVIVED (with the consumption-rule/doc nit; semantic soundness contingent on T-A2 building the documented model)

### `EllipticCurveGeom` (Basic.lean:71)
- Attacks: [4] Loeffler Def 3.3.1 verbatim (A1) says "proper and **flat** and all fibres are smooth genus 1 curves"; record demands `SmoothOfRelativeDimension 1 π` (strictly stronger than flat+smooth-fibres without lfp). Decomposition A1 pre-empts this with Loeffler's own Def 3.4.1 remark ("requires that ℰ → S be a smooth morphism") and KM 2.1.1 says smooth outright — recorded, not drift. → faithful
- Attacks: [2] `S = ∅`: E = ∅, all fields vacuous/hold — the empty family, standard-admissible. `S = Spec k`: reduces to a pointed smooth proper genus-1 curve over k — correct. Fibres are never empty (section meets every fibre), so no empty-fibre pathology in `fibres`. → survives
- Attacks: [3] No `Surjective π` (follows from the section), no connectedness of S, no separatedness (inside `IsProper`) — nothing missing, nothing redundant beyond the flagged smooth-vs-flat choice; `attribute [instance]` on `smooth`/`proper` is a sound projection-instance pattern. → minimal
- Verdict: SURVIVED

---

## GroupLaw.lean

### `EllipticCurve` (structure) (GroupLaw.lean:50)
- Attacks: [seed/5] `comm : letI := grp; IsCommMonObj (Over.mk π)` — `IsCommMonObj (X) [MonObj X]` (Mon.lean:1213) and `GrpObj extends MonObj` (Grp.lean:43): the `letI` installs `grp`, and the `MonObj` consumed is `grp.toMonObj` — the right instance, with no competing instance in scope; consumer `instance isCommMonObj := E.comm` re-aligns because `grpObj := E.grp` supplies the defeq-same `toMonObj`. → verified
- Attacks: [seed/5] `one_eq_zero`: unit object of `Over.cartesianMonoidalCategory` is literally `Over.mk (𝟙 S)` (Cartesian/Over.lean:34), so `(𝟙_ (Over S)).hom = 𝟙 S` and the equation pins `η.left = zero` on the nose; even under a different terminal choice, `.hom` of a terminal object of `Over S` is canonically an iso, so the comparison morphism is the right one in all cases. → correct comparison
- Attacks: [4] KM 1.4.1 ("smooth commutative S-group-scheme of relative dimension one") — record = geometry + `grp` + `comm` + unit-normalisation: matches the consumed object; making the group datum *data* (vs Abel-derived) is design D5, expert-confirmed, with canonicity theorems stated — no silent drift. → faithful
- Attacks: [1]/[2] Consistency at degenerate bases: S = ∅ ⟹ Over ∅ is equivalent to the trivial setting, trivial GrpObj satisfies all three fields; existence over general S is `abelEnrichment_exists` (true, KM 2.1.2). No inconsistent field combination found. → satisfiable
- Verdict: SURVIVED

### `asOver` (GroupLaw.lean:65) / `grpObj` (67) / `isCommMonObj` (69)
- Attacks: [5] `asOver` is a reducible abbrev of `Over.mk E.π`, so the `grpObj`/`isCommMonObj` instances key exactly where `Over.grpObjMkPullbackSnd` and `Hom.group/commGroup` need them; no other GrpObj instance on `Over.mk E.π` exists to diamond. → clean
- Attacks: [3] `isCommMonObj`'s implicit MonObj argument is `grpObj.toMonObj` — same instance as inside `comm`'s letI (defeq), so no instance mismatch. → verified
- Attacks: [2] Degenerate S: instances remain well-typed; nothing empty-hostile. → survives
- Verdict: SURVIVED (all three)

### `abelEnrichment_exists` (GroupLaw.lean:73)
- Attacks: [1] Truth over arbitrary bases: Abel `E(T) ≅ Pic⁰(E_T/T)` (KM 2.1.2 / GME 2.2, chain A6 fully transcribed in decomposition-gme2 with the COH/RR pins) — holds over any base scheme, non-reduced and disconnected included; no counterexample class known. → true
- Attacks: [3] No hidden hypotheses needed (no noetherian, no connectedness) — correct, since A6's proof route (COH-1/2/3 + RR box) is stated base-free; the seven named black boxes are registered in the module docstring, matching plan D5. → minimal
- Attacks: [4] Statement `∃ E, E.toEllipticCurveGeom = G` is the exact "admits an enrichment" form; source has statement-level KM 2.1.2 PENDING-SOURCE, GME 2.2.1–2.2.5 proofs transcribed but **no verbatim statement quote** in any decomposition doc. → quote gap
- Verdict: SURVIVED mathematically — QUOTE-MISSING(GME 2.2.5/KM 2.1.2 statement not quoted verbatim; gme2 has proof transcription only)

### `abelEnrichment_unique` (GroupLaw.lean:78)
- Attacks: [1] Truth: two commutative group structures with the same unit section on a proper smooth fibre-connected family coincide (rigidity; GME Cor 2.2.5, proof transcribed at gme2 A6.δ). Structure-equality `E = E'` reduces (Prop fields are proof-irrelevant) to `grp = grp'` over `h` — exactly rigidity. → true
- Attacks: [2] S = ∅ / trivial cases: unique trivial structure, equality holds. Char p: rigidity argument (λ ≡ 1 via COH-2) is characteristic-free. → survives
- Attacks: [3] Does it need `comm`? Cor 2.2.5's proof uses commutativity of one structure ("minus = Abel group!") — both records carry `comm`, so hypotheses suffice. → adequate
- Verdict: SURVIVED — QUOTE-MISSING(same status as `abelEnrichment_exists`)

### `mulBy` (GroupLaw.lean:84)
- Attacks: [seed/5] **The pointwise-vs-composition trap, resolved at source**: `letI : Group (E.asOver ⟶ E.asOver) := Hom.group` installs `CategoryTheory.Hom.group` whose monoid is `Hom.monoid` with `mul f₁ f₂ := lift f₁ f₂ ≫ μ` (Mon.lean:210) — the convolution/pointwise group of the group object, **not** `CategoryTheory.End`'s composition monoid; `letI` is innermost so it wins any resolution race, and `End X` is a distinct def that can't fire on `X ⟶ X` anyway. Hence `(𝟙 E.asOver) ^ n` = x ↦ xⁿ = [n]. → correct semantics
- Attacks: [2] n = 0 ⟹ unit of the Hom-group = `toUnit ≫ η` = (with `one_eq_zero`) π ≫ zero — the constant-zero endomorphism ✓; n = 1 ⟹ 𝟙 ✓; n = −1 ⟹ `𝟙 ≫ ι = ι` = inversion ✓ (`GrpObj.inv_eq_inv : ι = (𝟙 G)⁻¹`, Grp.lean:182, literally confirms). → correct at anchors
- Attacks: [4] KM 2.3 is ⧗-gated (do-not-formalize-from-memory); `mulBy` is a *definition* in the group object, not a KM 2.3 theorem — no gate violation; its theorems (Torsion.lean) are correctly marked PENDING-SOURCE. → compliant
- Verdict: SURVIVED

### `mulByHom` (GroupLaw.lean:89) / `mulByHom_π` (92)
- Attacks: [5] `mulByHom_π` is a real (non-sorry) proof via `Over.w` — true by the Over-category structure; checked shape `(mulBy n).left ≫ E.π = E.π`. → real
- Attacks: [2] n = 0: `mulByHom 0 ≫ π = π` consistent with constant-zero map. → survives
- Attacks: [3] No instance leakage: abbrev unfolds to `.left`, no extra hypotheses. → clean
- Verdict: SURVIVED (both)

### `Point` (GroupLaw.lean:97) / `zeroPoint` (101)
- Attacks: [4] Loeffler §3.3: E(T) over g = lifts of g through π — exact match, T-points relative to an arbitrary structure map g (not only 𝟙). → faithful
- Attacks: [2] `T = ∅`: unique point (unique `∅ ⟶ E.E`, condition forced) — E(∅) = 0 group, correct. `g = 𝟙 S`: sections, as intended. → survives
- Attacks: [1] `zeroPoint` = `g ≫ zero` with real proof — the correct basepoint (matches `one_eq_zero` normalisation through `pointAddCommGroup`'s unit: `g ≫ 𝟙 ≫ zero`). → coherent
- Verdict: SURVIVED (both)

### `pointEquivOverHom` (GroupLaw.lean:105)
- Attacks: [5] `Over.homMk`/`Over.w` round-trip, both inverses `rfl`-checked in source (real def, no sorry) — the canonical adjunction-free bijection. → real and canonical
- Attacks: [3] No noncomputable data smuggled: components are structure-shuffles; `noncomputable` marker only for elaboration convenience. → clean
- Attacks: [2] Degenerate g: works for any T, g, including empty T. → survives
- Verdict: SURVIVED

### `pointAddCommGroup` (GroupLaw.lean:115)
- Attacks: [5] Chain verified at source: `Hom.commGroup [IsCommMonObj]` (Grp.lean:306, braided context supplied by the file's local `Over.braidedCategory`) → `Additive.ofMul` → `Equiv.addCommGroup` (transfers **from target to source**, correct direction). Addition on points = pointwise μ-convolution of lifts = the fibrewise group law on T-points. → correct structure
- Attacks: [1] Instance placement: global instance on the subtype `{h // h ≫ E.π = g}` — keyed on E and g, no diamond with any other AddCommGroup on that subtype (none exists). → safe
- Attacks: [2] T = ∅: trivial group ✓; g = 𝟙 S: group of sections ✓; commutativity really consumed from `comm` (via `Hom.commGroup`'s `[IsCommMonObj]`), not assumed. → survives
- Verdict: SURVIVED

### `point_smul_eq_comp_mulBy` (GroupLaw.lean:123)
- Attacks: [1] Truth: precomposition `Hom(mk g, E) ← Hom(E,E)` is compatible with the convolution group; `P ≫ 𝟙ⁿ = (P ≫ 𝟙)ⁿ = Pⁿ`, and `n • (Additive-transported P) = Pⁿ` — the two sides agree; this is exactly `GrpObj.comp_zpow` (Grp.lean:177, exact statement `f ≫ g ^ n = (f ≫ g) ^ n`). → true, discharge verified
- Attacks: [2] n = 0: LHS = zeroPoint coercion = `g ≫ zero`; RHS = `P.1 ≫ (toUnit ≫ η).left` = `P.1 ≫ π ≫ zero` = `g ≫ zero` (uses `one_eq_zero`) ✓ consistent; n negative: inversion consistent via `comp_inv`. → anchors pass
- Attacks: [3] The `letI`-vs-instance alignment: the statement's `n • P` uses `pointAddCommGroup` and its RHS uses `mulBy`'s `letI` — both reduce to the same `Hom.monoid` powers (defeq through `Additive`), so the spec genuinely pins `mulBy` against the point-level action (its stated purpose). → coherent spec
- Verdict: SURVIVED

### `Point.restrict` (GroupLaw.lean:127)
- Attacks: [3] Contravariant functoriality along `k : T′ ⟶ T` to `Point (k ≫ g)` — right variance, real proof. → clean
- Attacks: [2] `k = 𝟙`: restricts to same point modulo `𝟙 ≫ g = g` — statement-level composition is definitional; fine. → survives
- Attacks: [1] Additivity of restriction not stated (restrict is a group hom) — spec gap for later naturality tickets, not a falsity. → note
- Verdict: SURVIVED

### `baseChange` (GroupLaw.lean:135)
- Attacks: [seed/5] `grp := Over.grpObjMkPullbackSnd` — **hover-equivalent source check**: needs `[GrpObj (Over.mk E.π)]` (found: the `grpObj` instance) and yields `GrpObj (Over.mk (pullback.snd E.π g))` = exactly the record's `π` field. Orientation correct: group leg first, base-change leg second. → verified
- Attacks: [5] The five Prop sorries are all dischargeable against present mathlib: `smoothOfRelativeDimension_isStableUnderBaseChange` (Smooth.lean:166), `IsProper` base-change instance, `isCommMonObj_mk_pullbackSnd` (Cartesian/Over.lean:311) for `comm`, `monObjMkPullbackSnd_one` + `E.one_eq_zero` for `one_eq_zero` (possible defeq-alignment lemma between `mapGrp`'s and `mapMon`'s MonObj needed — mechanical). → dischargeable
- Attacks: [1] `fibres` field: fibre of pullback over t = (fibre over g t) ⊗_{κ(gt)} κ(t); needs `IsWeierstrassModel` stability under residue-field extension + T-A4 uniqueness to transport the pointed iso — i.e. **its discharge route runs through the REJECTED `isWeierstrassModel_unique`**; base-change of the interface itself is fine (properness/lfp/points all stable using `(W.baseChange K′).baseChange L = W.baseChange L`), but the route must be re-verified after the T-A4 fix. → dependency flag
- Attacks: [2] `g = 𝟙 S`: base change along identity — record fields well-typed, `zero` reduces to graph lift; `T = ∅`: empty elliptic curve, consistent. → survives
- Verdict: SURVIVED (with the `fibres`-discharge dependency on fixing T-A4)

### `Point.asSection` (GroupLaw.lean:150)
- Attacks: [1] `pullback.lift P.1 (𝟙 T)` with `P.2` — the canonical graph section of `E ×_S T → T`; composing with `pullback.fst` recovers P.1 ✓. → correct
- Attacks: [3] Real def, no hypotheses beyond P — minimal. → clean
- Attacks: [4] Standard dictionary "T-point over g = section of base change" (Loeffler §3.3 usage) — faithful; the inverse direction (sections → points) not stated — coverage note only. → survives
- Verdict: SURVIVED

---

## Torsion.lean

### `NIsInvertible` (Torsion.lean:44)
- Attacks: [seed/1] `IsUnit (N : Γ(X,⊤))` vs "N invertible on X": a global section of O_X is a unit iff it is a unit in every stalk (inverses glue), so this ⟺ N ∉ 𝔪ₓ ∀x ⟺ X is a ℤ[1/N]-scheme — the standard meaning; equivalence holds for arbitrary (non-quasi-compact, disconnected) X. → equivalent
- Attacks: [2] `X = ∅`: Γ = 0-ring, `IsUnit 0` holds, "invertible on ∅" vacuously true — consistent. `N = 0`: `IsUnit 0` ⟺ Γ trivial ⟺ X = ∅ (stalks are nontrivial local rings) — consistent junk-freedom. → survives
- Attacks: [3] Consistency nit: `muNπ_etale_of_invertible` (MuN.lean:85) restates the same condition raw (`IsUnit (N : Γ(S,⊤))`) because MuN.lean doesn't import Torsion.lean — one concept, two spellings; move `NIsInvertible` to a shared low file. → nit
- Verdict: SURVIVED

### `torsion` (Torsion.lean:50)
- Attacks: [1] Kernel correctness: `pullback (E.mulByHom N) E.zero` = E ×_{[N],E,0} S — the scheme-theoretic kernel; with `mulBy` now verified pointwise, this is genuinely E[N], not a composition-power artifact. → correct
- Attacks: [2] N = 0: `[0] = π ≫ zero`, and (zero mono) the pullback is the graph of π ≅ E — the correct kernel of [0]; all downstream theorems guard with `NeZero`. N = 1: kernel of 𝟙 ≅ S ✓ rank 1 = 1². → consistent
- Attacks: [4] KM 2.3 / Loeffler §3.4 define E[N] as ker[N] — exact match; kernel-as-pullback-against-zero is also literally KM 1.6.1's square (km1 D-inc.4 confirms the skeleton's `pointToTorsion` squares are the intended ones). → faithful
- Verdict: SURVIVED

### `torsionι` (54) / `torsionπ` (58)
- Attacks: [5] Leg orientation: `fst → E.E` (base change of `zero` along [N]), `snd → S` (base change of [N] along `zero`) — matches both names and both downstream theorems (`ι` closed-immersion via zero's closed-immersion; `π` finite/étale via [N]'s properties). → correct legs
- Attacks: [2] N = 0/1 as above — names stay meaningful. → survives
- Attacks: [3] No hypotheses — correct (pure data). → clean
- Verdict: SURVIVED (both)

### `pointToTorsion` (64) / `pointToTorsion_torsionπ` (69)
- Attacks: [1] Universal-property packaging with hypothesis `x.1 ≫ [N] = g ≫ zero` — precisely "killed by N over g"; km1 D-inc.4 confirms this is the classifying-map formulation KM 1.6 needs ("pointToTorsion P hP is exactly the classifying map"). → correct
- Attacks: [5] Real defs, `pullback.lift`/`lift_snd` — present, simp lemma true by construction. → real
- Attacks: [3] The companion `pointToTorsion ≫ torsionι = x.1` (lift_fst) is NOT stated — half the universal property missing from the API surface; harmless now, needed by T-D17. → coverage note
- Verdict: SURVIVED (both; add the `lift_fst` companion when T-B tickets open)

### `torsionι_isClosedImmersion` (Torsion.lean:76)
- Attacks: [1] Truth: `zero` is a section of the separated (proper) π ⟹ closed immersion; `torsionι` is its base change along [N] ⟹ closed immersion. True for every N — including N = 0 (graph of π, an iso). → true
- Attacks: [3] `[NeZero N]` is **removable** (statement true at N = 0 as above) — stronger hypothesis than needed; not source-driven (no source states this with N ≥ 1 restriction). → weakening flag
- Attacks: [4] No verbatim quote anywhere in the decomposition docs (T-B3 has no leaf in R-B; decomposition-km1 D-curve.1 cites the mathlib pattern `isClosedImmersion_of_comp_eq_id` for the *section* half only). → quote gap
- Verdict: SURVIVED mathematically (drop `[NeZero N]`) — QUOTE-MISSING(no leaf/quote for T-B3 in any decomposition doc)

### `torsionπ_isFinite` (Torsion.lean:83)
- Attacks: [1] Truth: KM 2.3.1 standard — E[N] → S finite for N ≥ 1 over arbitrary base (properness of E[N] from ι closed + E proper; quasi-finite fibres; ZMT). N = 0 false (E[0] = E) ⟹ `NeZero` genuinely needed here. → true with right hypothesis
- Attacks: [5] Cited route verified: `IsFinite.of_isProper_of_locallyQuasiFinite [IsProper f] [LocallyQuasiFinite f]` present (ZariskisMainTheorem.lean:371) — exactly the B1 plan's ZMT step. → dischargeable
- Attacks: [4] B1 is explicitly PENDING-SOURCE(KM 2.3.1); no verbatim quote in any doc (Loeffler is only cited for the étale case). Statement matches the standard form; char p | N supersingular case correctly *included* (no invertibility hypothesis) — faithful to KM's point. → quote gap only
- Verdict: QUOTE-MISSING(KM 2.3.1 verbatim pending — statement itself survived all attacks)

### `torsionπ_flat` (Torsion.lean:85)
- Attacks: [1] Truth: KM 2.3.1; flatness of E[N]/S for N ≥ 1 (BB-FLAT/fibrewise criterion route, HB-FIBCRIT registered as T-FLAT1 — honestly flagged as absent from mathlib in km1). → true, route honest
- Attacks: [3] `[NeZero N]` removable (E[0] = E is flat — smooth); also decl has **no docstring** (only theorem in the file without one). → weakening + doc nit
- Attacks: [4] Same PENDING-SOURCE status as isFinite; note the pair (IsFinite, Flat) still under-states KM's "finite **locally free**": lfp is derivable (sections/cancellation from smooth π) but never stated — the "locally free" packaging of KM 2.3.1 has no Lean witness yet. → decomposition gap, minor since derivable
- Verdict: QUOTE-MISSING(KM 2.3.1 pending; drop `NeZero`, consider an lfp companion statement)

### `torsion_rank` (Torsion.lean:88)
- Attacks: [seed/5] `Scheme.Hom.finrank (f) (s) : ℕ` (FlatRank.lean:88) takes **no typeclass arguments** — the two `haveI`s are decorative (they neither enable elaboration nor change the value); statement is well-formed with or without them. finrank is the fibre rank, locally constant under finite+flat+lfp (`isLocallyConstant_finrank`) — the intended reading. → seed answered: no required instances
- Attacks: [1]/[2] N = 1: rank 1 ✓; char p | N supersingular: rank still N² (KM's headline) ✓ — no invertibility hypothesis, faithful; `S = ∅`: vacuous over s. No counterexample. → true
- Attacks: [4] PENDING-SOURCE(KM 2.3.1) — the rank-N² claim has no verbatim quote in any doc (Silverman III.6.2(d) fibrewise anchor cited but not quoted). → quote gap
- Verdict: QUOTE-MISSING(KM 2.3.1 pending — statement survived; optionally delete the decorative `haveI`s)

### `mulBy_etale` (Torsion.lean:95)
- Attacks: [4] Verbatim Loeffler 3.4.2(2) present in both the file docstring and decomposition B2 — statement matches ([N] étale when N invertible). Transcription defect in the quote itself: "If E/S is an elliptic curve and **N ≥ is invertible**" — dropped "1"; cosmetic but it *is* flagged as verbatim. → match, quote typo
- Attacks: [3] `[NeZero N]` redundant: given `h : NIsInvertible S N` with N = 0, Γ(S,⊤) is trivial ⟹ S = ∅ ⟹ E = ∅ ⟹ `Etale (∅ ⟶ ∅)` vacuously — hypothesis removable (harmless). → weakening flag
- Attacks: [2] char p bases with p ∤ N: étale ✓ (the [N]*ω = Nω argument, E15 in gme2, is the transcribed proof core — including for char p); p | N excluded by h ✓. → survives
- Attacks: [5] `Etale` class present (Morphisms/Etale.lean:41); gme2 E15 records the proof engine ("ALSO the proof core of T-B5!"). → dischargeable
- Verdict: SURVIVED

### `torsionπ_etale` (Torsion.lean:100)
- Attacks: [1] Truth: base change of the étale [N] along `zero` — stable ⟹ étale; combined with `torsionπ_isFinite` gives Loeffler's "finite étale". → true
- Attacks: [3] Same `NeZero`-redundancy as `mulBy_etale` (h forces S = ∅ at N = 0). → weakening flag
- Attacks: [4] No verbatim quote for this corollary anywhere (docstring cites "Loeffler §3.4; KM 2.3.5" as locators only; B2's quote covers [N], not E[N] → S). One-step corollary, but per the project's own gate it lacks its quote. → quote gap
- Verdict: QUOTE-MISSING(locators only; trivially derivable from quoted B2 + base change — attach Loeffler 3.4.2(3)-or-equivalent verbatim when cut)

---

## MuN.lean

### `muNRing` (MuN.lean:34)
- Attacks: [4] Loeffler §3.2 verbatim (decomposition B3): "F(R) = {n-th roots of unity in R} is represented by (Z[T]/(Tⁿ − 1), T)" — ring matches exactly; `ULift` is universe hygiene consistent with `Spec (ULift ℤ)` being terminal in `Scheme.{u}`. → faithful
- Attacks: [2] N = 0: `T⁰ − 1 = 0`, ring = ℤ[T], μ₀ = 𝔸¹ ≠ 𝔾ₘ (the "order dividing 0" reading would demand 𝔾ₘ) — junk at N = 0, but every consumer guards with `NeZero`. N = 1: ℤ[T]/(T−1) ≅ ℤ, μ₁ trivial ✓. → guarded
- Attacks: [3] No `NeZero` on the def itself — correct placement (data total, properties guarded). → clean
- Verdict: SURVIVED

### `muNAbs` (MuN.lean:39)
- Attacks: [1] `Spec (muNRing N)` — the affine scheme of KM 1.12; nothing to falsify at data level. → clean
- Attacks: [2] Same N = 0/1 degeneracies as `muNRing`, guarded downstream. → survives
- Attacks: [4] KM 1.12 quote itself PENDING (preview doesn't reach 1.12, recorded in B3) — but [Loe] verbatim covers the representing object, which is this def. → sourced via Loe
- Verdict: SURVIVED

### `muN` (MuN.lean:43)
- Attacks: [seed/5] `pullback (terminal.from S) (terminal.from (muNAbs N))`: `instance : HasTerminal Scheme` present (AlgebraicGeometry/Limits.lean:59, terminal = Spec(ULift ℤ)); `Limits.terminal.from` type-correct; scheme pullbacks exist — the whole expression is well-typed (confirmed by fresh olean). Pullback over the terminal = binary product S ×_{Spec ℤ} μ_N — the correct μ_{N,S}. → seed verified
- Attacks: [2] N = 0: 𝔸¹_S (see muNRing note); S = ∅: μ_{N,∅} = ∅ ✓; N = 1: ≅ S ✓. → consistent
- Attacks: [3] No `NeZero` — correct (data). → clean
- Verdict: SURVIVED

### `muNπ` (MuN.lean:47)
- Attacks: [5] `pullback.fst` — first leg belongs to `terminal.from S`, so fst lands in S ✓ (orientation right; snd would land in μ_N^abs). → correct leg
- Attacks: [2] Degenerate cases inherit from `muN` ✓. → survives
- Attacks: [1] This is the structure morphism KM 1.12 intends (projection of base change) ✓. → faithful
- Verdict: SURVIVED

### `constScheme` (MuN.lean:52)
- Attacks: [4] KM 1.4.4(5) "the constant S-scheme ℤ/Nℤ" (quoted in module docstring) — disjoint union of A-many copies ✓ `∐`. → faithful
- Attacks: [5] `∐ fun _ : A ↦ S` needs `HasColimitsOfShape (Discrete A) Scheme.{u}` for `[Small.{u} A]` (Limits.lean:187) — A : Type 0 is always u-small ✓ compiles. → verified
- Attacks: [3] `[Finite A]` is **removable** (schemes have arbitrary small disjoint unions) and `A : Type` is universe-rigid — harmless for `ZMod N` but flagged; A needs no group structure here (correct: group enters only at `constZModGrpObj`). → minor over-hypothesis
- Attacks: [2] A = Empty: ∅ ✓; A = trivial group carrier: S ✓. → survives
- Verdict: SURVIVED

### `constSchemeπ` (MuN.lean:56)
- Attacks: [1] `Sigma.desc (fun _ ↦ 𝟙 S)` — fold of identities, the correct structure map ✓. → clean
- Attacks: [2] Empty A: unique map from ∅ ✓. → survives
- Attacks: [3] Hypotheses inherited from constScheme only ✓. → clean
- Verdict: SURVIVED

### `muNGrpObj` (MuN.lean:61) — DS3, sorriness not at issue
- Attacks: [3] `[NeZero N]` is **load-bearing against a junk-but-satisfiable instance**: at N = 0, `GrpObj (Over.mk (muNπ S 0))` would be *satisfiable* (𝔸¹_S carries 𝔾ₐ!) but with a group law violating the docstring's pin "comultiplication Spec of T ↦ T ⊗ T" (which is not a Hopf structure on ℤ[T]). NeZero correctly forecloses the junk instantiation. → hypothesis justified
- Attacks: [4] Spec pin (T ↦ T ⊗ T) matches KM 1.12/standard μ_N Hopf algebra; the DS register's pinning for DS3 routes through `muNPointsEquiv`-naturality (T-B2) — adequate *provided* the naturality specs actually get stated (currently only promised in ticket text, no sorried Lean statement `muNPointsEquiv_natural` exists in the file). → spec-surface gap flag
- Attacks: [1] Instance-with-sorried-data: usable but any downstream `simp`/defeq on its fields is vacuous — consistent with the register's "use only through stated specifications" rule; no consumer in the five files violates it. → contained
- Verdict: SURVIVED (add the promised `muNPointsEquiv_natural` skeleton statement so DS3's pin is Lean-visible, per plan.md's own register rule (iii))

### `constZModGrpObj` (MuN.lean:66) — DS3
- Attacks: [3] `[NeZero N]` doubly needed: `Finite (ZMod 0)` fails (ℤ), and the group pin is ℤ/N. → justified
- Attacks: [4] KM 1.4.4(5) ✓; the km1 plan (D6 (5)⟹(1)) consumes exactly this instance + a transport lemma — consistent forward reference. → coherent
- Attacks: [2] N = 1: one copy of S, trivial group object ✓ satisfiable. → survives
- Verdict: SURVIVED

### `muNPointsEquiv` (MuN.lean:76) — DS3
- Attacks: [seed/1] Should the RHS depend on g? **No, and it correctly doesn't**: Hom(T, S ×_⊤ μ_N^abs) ≅ Hom(T,S) × Hom(T, μ_N^abs) (terminal-compatibility automatic), so the fibre over g is Hom(T, μ_N^abs) ≅ Hom_ring(ℤ[T]/(T^N−1), Γ(T,O_T)) ≅ {a | a^N = 1} — independent of g, for every g. The g-dependence lives (only) in the LHS subtype, as written. → seed verified, statement true
- Attacks: [3] `[NeZero N]` removable by coincidence: at N = 0 LHS ≅ Hom_S(T, 𝔸¹_S) ≅ Γ(T,⊤) and RHS = {a | a⁰ = 1} = Γ(T,⊤) — still equinumerous/equivalent; harmless narrowing. → minor
- Attacks: [4] Loeffler §3.2 verbatim ✓ (B3); naturality in T and g and the group-compatibility (equiv is a group iso onto μ_N(Γ)) are deferred to T-B2 with the register's blessing — but as with DS3a, no sorried Lean naturality statement exists yet. → spec-surface gap flag (shared with muNGrpObj)
- Attacks: [2] T = ∅: LHS singleton, Γ(∅) = 0-ring, RHS = {0} with 0^N = 0 = 1 ✓ singleton — consistent. → survives
- Verdict: SURVIVED

### `muNπ_isFinite` (MuN.lean:82)
- Attacks: [1] Truth: Spec of a rank-N free ℤ-algebra base-changed — finite for N ≥ 1; N = 0 false (𝔸¹) ⟹ NeZero needed ✓. → true
- Attacks: [4] T-B7's docstring promises "finite locally free of rank N, étale **iff** N invertible" — the Lean surface has only `IsFinite` + the ⟸ étale direction: **no flatness statement, no rank-N statement, no iff-converse** anywhere in the file. The module docstring's "finite locally free of rank N" claim has no Lean witness. Also no verbatim source quote (KM 1.12 not in the preview; Loeffler's §3.2 quote covers representability, not finiteness). → coverage + quote gap
- Attacks: [2] S = ∅ vacuous ✓; N = 1: iso ⟹ finite ✓. → survives
- Verdict: QUOTE-MISSING(KM 1.12 pending; also add `muNπ_flat`/`muNπ_finrank` skeleton statements to match the T-B7 docstring, or weaken the docstring)

### `muNπ_etale_of_invertible` (MuN.lean:84)
- Attacks: [1] Truth: T^N − 1 separable over Γ when N invertible ⟹ μ_N,S → S étale ✓ (standard); converse (étale ⟹ invertible, for S ≠ ∅) promised by "iff" in docstring but not stated — one-directional statement is TRUE as written. → true
- Attacks: [3] `NeZero` redundant given h (IsUnit 0 ⟹ S = ∅ ⟹ vacuous); uses raw `IsUnit (N : Γ(S,⊤))` instead of `NIsInvertible` (layering: MuN doesn't import Torsion) — same condition, two spellings. → nits
- Attacks: [2] char p | N with h: impossible (p not invertible on 𝔽_p-points) — correctly excluded semantically; S = Spec ℤ, N ≥ 2: h fails, no claim — correct (μ_N/ℤ is not étale). → survives
- Attacks: [4] No verbatim quote (KM 1.12 pending; "standard"). → quote gap
- Verdict: QUOTE-MISSING(KM 1.12 pending; statement survived — consider stating the converse to honor the "iff" or trimming the docstring)

---

## Summary table

| Decl | Verdict |
|---|---|
| `SpecPoints` | SURVIVED |
| `IsWeierstrassModel` | **NEEDS-FIX** (points: unnatural/unpointed `Nonempty(≃)`; nonsingular-only comparison type; no smoothness field) |
| `projModel` (DS1) | SURVIVED (doc drift: charts vs adopted Proj route) |
| `projModelπ` (DS1) | SURVIVED |
| `projModelZero` (DS1) | SURVIVED (under-pinned pending points fix) |
| `projModel_isWeierstrassModel` | **REJECTED** (false for singular W: cuspidal y²=x³/𝔽₅ has 6 model points vs 5 in `Affine.Point`; fix: `[W.IsElliptic]`) |
| `projModel_smooth` | SURVIVED |
| `isWeierstrassModel_unique` | **REJECTED** (V(F) ≇ V(F²) over ℚ both satisfy the interface; fix: `[W.IsElliptic]` + smoothness of f, f′) |
| `sectionFiberPoint` | SURVIVED |
| `FibrewiseElliptic` | SURVIVED (pointedness clause correctly oriented; ∀ s over all points faithful) |
| `EllipticCurveGeom` | SURVIVED |
| `EllipticCurve` (structure) | SURVIVED (letI/IsCommMonObj instance path and `(𝟙_).hom ≫ zero` comparison both verified right) |
| `asOver` / `grpObj` / `isCommMonObj` | SURVIVED |
| `abelEnrichment_exists` | SURVIVED / QUOTE-MISSING |
| `abelEnrichment_unique` | SURVIVED / QUOTE-MISSING |
| `mulBy` | SURVIVED (pointwise Hom-group confirmed at mathlib source — 𝟙^n = [n], not End-composition) |
| `mulByHom`, `mulByHom_π` | SURVIVED |
| `Point`, `zeroPoint` | SURVIVED |
| `pointEquivOverHom` | SURVIVED |
| `pointAddCommGroup` | SURVIVED |
| `point_smul_eq_comp_mulBy` | SURVIVED (`GrpObj.comp_zpow` exact match) |
| `Point.restrict` | SURVIVED |
| `baseChange` | SURVIVED (`grpObjMkPullbackSnd` orientation verified; `fibres` discharge depends on fixed T-A4) |
| `Point.asSection` | SURVIVED |
| `NIsInvertible` | SURVIVED |
| `torsion`, `torsionι`, `torsionπ` | SURVIVED |
| `pointToTorsion`, `pointToTorsion_torsionπ` | SURVIVED |
| `torsionι_isClosedImmersion` | SURVIVED (drop `NeZero`) / QUOTE-MISSING |
| `torsionπ_isFinite` | QUOTE-MISSING (statement survived) |
| `torsionπ_flat` | QUOTE-MISSING (statement survived; drop `NeZero`; no docstring) |
| `torsion_rank` | QUOTE-MISSING (statement survived; `haveI`s decorative — finrank needs no instances) |
| `mulBy_etale` | SURVIVED (`NeZero` redundant given h) |
| `torsionπ_etale` | QUOTE-MISSING (statement survived) |
| `muNRing`, `muNAbs`, `muN`, `muNπ` | SURVIVED (`terminal.from`/`HasTerminal Scheme` verified) |
| `constScheme`, `constSchemeπ` | SURVIVED (`Finite` removable) |
| `muNGrpObj` (DS3) | SURVIVED (NeZero load-bearing vs 𝔾ₐ-junk; state the promised naturality skeleton) |
| `constZModGrpObj` (DS3) | SURVIVED |
| `muNPointsEquiv` (DS3) | SURVIVED (RHS correctly g-independent) |
| `muNπ_isFinite` | QUOTE-MISSING (+ missing flat/rank companions promised by docstring) |
| `muNπ_etale_of_invertible` | QUOTE-MISSING (docstring "iff" vs one-direction statement) |

## QUOTE-MISSING list (no verbatim source quote in any decomposition doc; plumbing defs exempted)
`isWeierstrassModel_unique` (A4, self-acknowledged PENDING-SOURCE(KM 2.2.5)) · `abelEnrichment_exists` · `abelEnrichment_unique` (GME 2.2.5 proof transcribed in gme2 A6.δ but no verbatim statement quote; KM 2.1.2 pending) · `torsionι_isClosedImmersion` (T-B3 has no decomposition leaf at all) · `torsionπ_isFinite` · `torsionπ_flat` · `torsion_rank` (B1, PENDING-SOURCE(KM 2.3.1)) · `torsionπ_etale` (T-B5′, locators only) · `muNπ_isFinite` · `muNπ_etale_of_invertible` (KM 1.12 not in preview).

## Headline findings (new, beyond known-fixed DEF-1/2/3)
1. **DEF-class: `IsWeierstrassModel.points` is a mere `Nonempty(≃)` per field** — the docstring's "naturally in K and sending x₀ to 0" was silently dropped in Lean. Consequences: (a) `projModel_isWeierstrassModel` is **false for singular W** against the registered DS1 construction (𝔽₅ cusp count 6 ≠ 5); (b) `isWeierstrassModel_unique` is **false outright** (reduced model vs its first-order thickening V(F²): same field-points, both proper/lfp/sectioned, non-isomorphic) — and no field-points-only upgrade can save uniqueness; a smoothness (or equivalent geometric) hypothesis is required, matching KM 2.2.5's actual scope. T-A2/T-A4/A5-`fibres` all sit downstream of this fix.
2. All seeded discharge names exist and are correctly oriented (`grpObjMkPullbackSnd`, pointwise `Hom.group`, `GrpObj.comp_zpow`, instance-free `Scheme.Hom.finrank`, `HasTerminal Scheme`, `Equiv.addCommGroup`, `Additive.ofMul`, `Module.free_of_flat_of_isLocalRing`, ZMT, `Scheme.GlueData`, `smoothOfRelativeDimension_isStableUnderBaseChange`, `Algebra.norm`); mathlib additionally already has `isCommMonObj_mk_pullbackSnd`/`monObjMkPullbackSnd_one` for T-A5's `comm`/`one_eq_zero`.
3. Minor systematic: removable `[NeZero N]` on `torsionι_isClosedImmersion`/`torsionπ_flat`/`mulBy_etale`/`torsionπ_etale`/`muNPointsEquiv`/`muNπ_etale_of_invertible`; MuN's T-B7 docstring promises flat/rank-N/iff with no Lean witnesses; `projModel` docstring still describes the superseded chart-gluing route; DS3's promised naturality specs have no sorried Lean skeletons yet (register rule (iii) exposure).