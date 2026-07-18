<!-- Adversarial /develop --decompose attack log, agent a8885de69a378fe0b, archived 2026-07-06 -->

All checks are complete. Here is the adversarial verification report.

---

# ADVERSARIAL VERIFICATION (red team) — `Moduli/EllCategory.lean`, `Moduli/Representability.lean`

**Repo**: `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (read-only pass; no edits, no builds).
**Files** (abbreviated below as `EC` and `RP`):
- `projects/ModularCurves/ModularCurves/Moduli/EllCategory.lean`
- `projects/ModularCurves/ModularCurves/Moduli/Representability.lean`

**Tool-discharged mathlib conventions** (via `lean_hover_info` on the target files + mathlib source in `.lake/packages/mathlib`, pin per `plan.md`):
- `CategoryTheory.IsPullback fst snd f g` = square `fst≫f = snd≫g` with `P→X` horizontal, `P→Y` vertical (hover, `IsPullback/Defs.lean`); `lift/lift_fst/lift_snd` at `Defs.lean:106–116`; `of_horiz_isIso` (`Basic.lean:77`), `paste_horiz` (`:190`), `of_right` (`:230`).
- `WeierstrassCurve.Ψ (n : ℤ) : R[X][Y]`; `Ψ_two : W.Ψ 2 = W.ψ₂` where `ψ₂ := W.toAffine.polynomialY = C (C 2) * Y + C (C W.a₁ * X + C W.a₃)` — the **y-involving** `2y + a₁x + a₃`; `Ψ_three : W.Ψ 3 = C W.Ψ₃` with `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` (univariate); `Ψ₂Sq` is the separate squared univariate (not used — correctly).
- `Polynomial.evalEval x y p = p(x,y)` with `x` bound to inner `X`, `y` to outer `Y` — pinned by mathlib's own `evalEval_polynomialY x y = 2*y + a₁*x + a₃`.
- `VariableChange` SMul: `vc • W` has `a₁' = u⁻¹(a₁+2s)`, …, i.e. `(X,Y) ↦ (u²X+r, u³Y+u²sX+t)`; so a point `(x,y)` maps to `(u⁻²(x−r), u⁻³(y−t−s(x−r)))`, hence `(x,y) ↦ (0,0) ⟺ r = x ∧ t = y`.
- `WeierstrassCurve.map_Δ : (W.map f).Δ = f W.Δ` (`Weierstrass.lean:273`); `MvPolynomial.eval₂Hom`, `Localization.Away`, `IsLocalization.Away.lift (hg : IsUnit (g x))` all present.
- `Functor.RepresentableBy (F : Cᵒᵖ ⥤ Type v) (Y : C)` with `homEquiv {X} : (X ⟶ Y) ≃ F.obj (op X)` — fully universe-polymorphic (`Equiv` crosses universes); mathlib also has `Functor.IsRepresentable := ∃ Y, Nonempty (F.RepresentableBy Y)` (`Yoneda.lean:520`).
- `AlgebraicGeometry.Smooth` (`Morphisms/Smooth.lean:62`, class) and `IsAffineHom` (`Morphisms/Affine.lean:47`, class) exist as morphism properties.
- `↾f = TypeCat.ofHom f` — in current mathlib, `Type u`-homs are `TypeCat.Hom` wrappers, so `↾` is necessary and correct in the functor `map` fields.

**Source of record**: Loeffler quotes re-extracted verbatim from `refs/ModularCurves/modcurvesnotes.pdf` (pdftotext), resolving the ellipses in `decomposition.md`. KM Ch. 2–14 not in `refs/` (only the Ch. 1 preview) — all KM 4.x locators remain PENDING-SOURCE.

---

## `EllObj` (EC:38)

**Attack 1 (source drift — object data).** Loeffler 3.7.1: "objects are diagrams E→S, S some R-scheme, E an elliptic curve over S." Our object = `base` + `structMap : base ⟶ Spec R` + `curve : EllipticCurve base` where `EllipticCurve` is the *working record* (`GroupLaw.lean:50`) carrying `grp/comm/one_eq_zero` **data** beyond the sources' geometric object. Two enrichments of the same geometry are distinct objects until `abelEnrichment_unique` (sorried) collapses them. *Outcome*: deliberate design D5; `EllHom` never mentions `grp`, so duplicated objects are canonically isomorphic (identity square) — harmless for representability-type statements, and moduli values use the group only through `Section`-smul. Deviation already registered in plan.md D5.

**Attack 2 (edge cases).** Empty base is allowed (elliptic curve over ∅ is vacuously a working record); `R = 0` gives a category of empty objects only. Checked: `representable_iff` remains consistent there (see that block). No degenerate-object pathology.

**Attack 3 (universes / typeclass).** `EllObj R : Type (u+1)` (contains `Scheme.{u}`); homs land in `Type u`; needed for `ModuliProblem = ⥤ Type u`. Verified consistent (`RepresentableBy` is universe-polymorphic). No missing coherence between `structMap` and `curve` is required by the source — correct.

**Verdict: SURVIVED.**

---

## `EllHom` (EC:50)

**Attack 1 (mathlib convention — `IsPullback` argument order).** `isPullback : IsPullback top X.curve.π Y.curve.π baseHom` unfolds to: square `top ≫ Y.π = X.π ≫ baseHom`, with `X.E` the limit of the cospan `Y.E → Y.base ← X.base`, i.e. **`X.E ≅ Y.E ×_{Y.base} X.base = E' ×_T S`** — exactly Loeffler's condition, in the right order. Hover-verified. **Discharged.**

**Attack 2 (the `zero_w` adjudication — is it in the source? is it automatic?).**
- *Loeffler-literal*: PDF lines 1435–1446 — the ellipsis in the docstring quote is **only the square diagram**; there is **no zero-section clause** in Loeffler's text. KM 4.1 is not in `refs/` (QUOTE-MISSING).
- *Is it automatic?* **No.** Counterexample: `S = T = Spec k`, `baseHom = 𝟙`, `top = τ_P` (translation by `0 ≠ P ∈ E(k)`): `τ_P` is an iso over `𝟙`, so the square is cartesian (`IsPullback.of_horiz_isIso`), but `zero ≫ τ_P ≠ zero`. So requiring `zero_w` genuinely shrinks hom-sets relative to the literalist reading.
- *Which category do the sources mean?* The zero-inclusive one. Three independent forcings: (i) an "elliptic curve" in KM 2.1.1/Loeffler 3.3.1 is the pair (E/S, 0), so "E ≅ E′ ×_T S" means iso *of elliptic curves*, i.e. pointed (Deligne–Rapoport / Stacks-project `M_ell` morphisms preserve the section); (ii) without `zero_w`, `gammaOneNaiveProblem`/`gammaFullNaiveProblem` are not even functors — pulling a section along a translation square destroys the torsion conditions, so `map`'s subtype sorries would be **unprovable**; (iii) with translations admitted, `Aut(E/S)` over `𝟙` contains all translations by `E(S)`, Loeffler's Exercise "(1) any representable functor is rigid" fails, and Thm 3.7.4 becomes false. Hence `zero_w` is the unique reading under which the source's own theorems are true: a **faithful disambiguation, not drift**.

**Attack 3 (hypothesis independence).** Neither Prop implies the other: `zero_w` without cartesian — take `top := π ≫ (baseHom ≫ Y.zero)`-type degenerate squares (zero-compatible, not pullbacks); cartesian without `zero_w` — the translation above. Both conditions are load-bearing. Also checked: no group-hom condition on `top` is required — matches the sources (group compatibility of pointed cartesian squares is automatic mathematically, and correctly *not* assumed).

**Attack 4 (edge).** `base_w` orientation `baseHom ≫ Y.structMap = X.structMap` = "square of R-scheme maps" ✓; `zero_w` orientation `X.zero ≫ top = baseHom ≫ Y.zero` typechecks on both sides as `X.base ⟶ Y.E` ✓.

**Verdict: SURVIVED** — with two required follow-ups: (a) docstring should state explicitly that the zero-compatibility clause is *not* in Loeffler's display but is implicit in "elliptic curve = (E, 0)" and is forced by 3.7.3/3.7.4 (record the translation counterexample); (b) KM 4.1 verbatim reconciliation stays on the QUOTE-MISSING list.

---

## `instance : Category (EllObj R)` (EC:61)

**Attack 1 (dischargeability of the 5 sorries).** `id.isPullback = IsPullback (𝟙 E) π π (𝟙 S)`: `IsPullback.of_horiz_isIso ⟨by simp⟩` — present. `comp.isPullback`: `f.isPullback.paste_horiz g.isPullback` gives `IsPullback (f.top ≫ g.top) X.π Z.π (f.baseHom ≫ g.baseHom)` — present (`Basic.lean:190`), matching orientation. `id_comp/comp_id/assoc`: `attribute [ext] EllHom` generates ext on the two data fields (Prop fields proof-irrelevant), so `ext <;> simp`. All plumbing sorries have named mathlib discharge paths. **Discharged.**

**Attack 2 (Prop-vs-data sorry audit).** `IsPullback` is a Prop-structure, so no data-sorry escapes the register — compliant with plan.md's DS rule.

**Attack 3 (edge: hom equality semantics).** Seed question: could `e ≠ Iso.refl` with `e.hom` differing "only in proof fields"? No — `EllHom` equality is `(baseHom, top)`-equality by ext + proof irrelevance; iso equality is hom-equality. The `Rigid` quantification below is therefore well-posed.

**Verdict: SURVIVED.**

---

## `ModuliProblem` (EC:82)

**Attack 1 (source).** "Contravariant functor Ell/R → Set" = `(EllObj R)ᵒᵖ ⥤ Type u` ✓ (Loeffler 3.7.1(2), verbatim re-checked).
**Attack 2 (universe).** Large source category (`Type (u+1)`) with `Type u` homs, `Type u` values: exactly the shape Yoneda/`RepresentableBy` supports; consistent with the size caveat Loeffler himself makes in §3.2.
**Attack 3 (design consistency).** Set-valued here vs. design D6 "groupoid-valued internally": both layers exist (`Moduli/Groupoid.lean`); this file is the KM set-valued engine, per plan D3. No conflict.
**Verdict: SURVIVED.**

---

## `EllObj.pullbackAlong` (EC:88)

**Attack 1 (data correctness).** `base := T`, `structMap := g ≫ X.structMap`, `curve := X.curve.baseChange g` with `baseChange` = `pullback E.π g` + `pullback.snd` (`GroupLaw.lean:135`) — total space `E ×_S T` over `T`: matches "P(E ×_S T / T)".
**Attack 2 (edge).** No pseudo-functoriality claimed (`pullbackAlong (𝟙)` is only isomorphic to `X`, not equal) — nothing downstream assumes strictness; `RelativelyRepresentable` only uses the single-step comparison. Safe.
**Attack 3 (hypothesis strength).** `g` arbitrary (not required flat/etc.) — correct: base change of elliptic curves needs no hypothesis.
**Verdict: SURVIVED.**

---

## `EllObj.pullbackAlongMap` (EC:96)

**Attack 1 (direction).** Goes `X.pullbackAlong (k ≫ g) ⟶ X.pullbackAlong g` — the Ell/R-morphism *from* the further pullback, so `P.map (….op)` restricts `P(E×_S T) → P(E×_S T')`: the correct contravariant restriction. Type-checked against the naturality clause below.
**Attack 2 (top map).** `pullback.map _ _ _ _ (𝟙 _) k (𝟙 _)` with the two `simp` squares: the canonical comparison `E ×_S T' → E ×_S T` over `k`. Correct instance of mathlib's `pullback.map`.
**Attack 3 (sorries dischargeable).** `isPullback`: the big square (`pullbackAlong (k≫g)` over `g∘k`) is `paste` of the wanted square with `(X.curve.baseChange g).isPullback`-type square; `IsPullback.of_right` (present, `Basic.lean:230`) closes it. `zero_w`: `pullback.hom_ext` + `lift_fst/lift_snd` computation. Both routine.
**Verdict: SURVIVED.**

---

## `ModuliProblem.Representable` (EC:107)

**Attack 1 (universe/typecheck).** `P.RepresentableBy X` for `P : (EllObj R)ᵒᵖ ⥤ Type u`: `homEquiv : (Y ⟶ X) ≃ P.obj (op Y)` is `Type u ≃ Type u` — verified against the mathlib source; no universe obstruction (seed discharged).
**Attack 2 (duplication).** The definition is verbatim mathlib's `Functor.IsRepresentable` (`Yoneda.lean:520–521`). Not an error, but a re-definition of an existing mathlib Prop — should be `abbrev`/`:= P.IsRepresentable` or deleted in favour of the mathlib name (AINTLIB reuse rule).
**Attack 3 (source fidelity).** Representable *by an `EllObj`* = "representable" in Loeffler 3.7.1(3); the representing object being a pair (base, universal curve) is exactly KM's packaging, later consumed by `gammaOneNaive_representable`'s `X.structMap` conjunct. Correct shape.
**Verdict: SURVIVED** (with dedup recommendation).

---

## `ModuliProblem.RelativelyRepresentable` (EC:114)

**Attack 1 (source drift).** Loeffler 3.7.1(3): "for every E/S ∈ Ob(Ell/R), the functor Sch/S → Set, T ↦ P(E ×_S T /T) is representable." Ours: `∃ Z, f : Z ⟶ X.base` with `{h : T ⟶ Z // h ≫ f = g} ≃ P(op (X.pullbackAlong g))` — `Hom_S(T, Z)` in subtype form: exact match, including the S-scheme structure of `Z` via `f`.
**Attack 2 (naturality clause completeness/direction).** Clause: `eqv (k ≫ g) ⟨k ≫ h.1, _⟩ = P.map (X.pullbackAlongMap g k).op (eqv g h)`. Every `Over (X.base)`-morphism is of the form `k : (T', k≫g) → (T, g)` up to propositional equality of the anchor, so this *is* full naturality of the representation, not a fragment; the direction (restrict the hom ↦ `P.map` of the comparison) is the correct contravariance (seed discharged; types re-derived by hand). Without this clause the definition would be a junk pointwise-bijection statement — its presence passes the project's own honesty gate.
**Attack 3 (edge).** `T` ranges over all `Scheme.{u}` with a map to `X.base` — Sch/S in the same universe, matching the source; `∃ eqv : (∀ {T} g, … ≃ …), …` is `Exists` over data, valid as a Prop.
**Attack 4 (hypothesis strength).** No étaleness/affineness is baked in (Loeffler 3.8.2 proves étale in the Γ-case; the *definition* rightly doesn't demand it).
**Verdict: SURVIVED.**

---

## `ModuliProblem.Rigid` (EC:126)

**Attack 1 (group identification).** Quantifies `e : X ≅ X` with `e.hom.baseHom = 𝟙`. Claim: this set = `Aut(E/S)` (pointed S-automorphisms). Both inclusions verified: an Ell/R-iso over `𝟙` has iso `top` with `zero ≫ top = zero`; conversely a pointed S-auto yields an `EllHom` (cartesian by `of_horiz_isIso`) which is an Ell/R-iso. With `zero_w` in `EllHom` this is exactly KM/Loeffler's `Aut(E/S)`; *without* `zero_w` it would contain all translations and `Rigid` would be unsatisfiable for the level problems — cross-confirms the `EllHom` adjudication. (Seed "HomOver vs Ell-isos with base 𝟙": same group.)
**Attack 2 (refl comparison).** `e ≠ Iso.refl X ⟺ e.hom ≠ 𝟙 ⟺ e.hom.top ≠ 𝟙` (given base `𝟙`): iso equality is hom equality; `EllHom` ext is on the two data fields; inverses are determined (`hom_inv_id` also forces `e.inv.baseHom = 𝟙`). No proof-field phantom distinctions possible.
**Attack 3 (semantics of "without fixed points").** Literal reading would outlaw the identity's fixed points; the def correctly formalises the standard reading (free action: every non-identity element moves every point). Since `e ↦ e⁻¹` permutes non-identity elements, using `P.map e.hom.op` (right action) instead of the inverse (left action) states the same freeness. Empty `P(E/S)` is vacuously free on both readings.
**Verdict: SURVIVED.**

---

## `ModuliProblem.representable_iff` (EC:135)

**Attack 1 (source).** Verbatim Loeffler Thm 3.7.4 ("(Katz–Mazur) P is representable if and only if it is relatively representable and rigid") — re-extracted from the PDF ✓. KM 4.7 locator PENDING-SOURCE (already flagged).
**Attack 2 (sanity counterexample sweep).** (i) Terminal presheaf over `R = ℤ`: RelRep holds (`Z := S`), Rigid fails (`[−1]` fixes the singleton) ⟹ RHS false; LHS false ("the Y that does not exist") — consistent. (ii) Over `R = 0`: all objects empty and mutually terminal; all three Props hold — consistent. (iii) Empty presheaf: not RelRep (value at the empty object vs `Hom(∅,Z)` singleton), not representable — consistent. The iff survives its cheapest falsifiers, including the forward direction (representable ⟹ RelRep, part of KM's iff).
**Attack 3 (proof-plan feasibility).** ⟸ needs `ℤ[1/2]/ℤ[1/3]` bootstraps + quotients: `(2,3) = (1)` so `Spec R[1/2] ∪ Spec R[1/3] = Spec R` for arbitrary `R` — the glue covers; AG-QUOT dependency is declared in the docstring. Honest.
**Verdict: SURVIVED** (QUOTE-MISSING: KM 4.7).

---

## `WeierstrassCurve.IsTateNormal` (RP:44)

**Attack 1 (coefficient dictionary vs Def 3.3.3).** PDF verbatim: `Y²Z + αXYZ + βYZ² = X³ + βX²Z`. Affine: `y² + αxy + βy = x³ + βx²` ⟹ `a₁ = α, a₃ = β, a₂ = β, a₄ = a₆ = 0`. Predicate `a₂ = a₃ ∧ a₄ = 0 ∧ a₆ = 0` with `a₁` free: exact. (Seed discharged.)
**Attack 2 (edge).** Allows `β = 0` (then Δ = 0, not elliptic) — correct: Loeffler defines `E(α,β)` for all `(α,β)` and imposes `Δ ∈ Γˣ` separately; ellipticity is imposed at use-sites.
**Attack 3 (namespace/style).** `_root_.WeierstrassCurve.IsTateNormal` extends the mathlib namespace from a project — acceptable per mathlib conventions; no clash found in mathlib.
**Verdict: SURVIVED.**

---

## `NowhereOrderLEThree` (RP:53)

**Attack 1 (indexing/normalisation — the seed's "high value target").** Tool-verified: `Ψ 2 = ψ₂ = 2y + a₁x + a₃` (the y-involving one, NOT the univariate `Ψ₂Sq`), `Ψ 3 = C Ψ₃` (univariate quartic), and `evalEval x y` puts `x` in the x-slot (pinned by `evalEval_polynomialY`). So the def is literally `IsUnit(ψ₂(x,y)·ψ₃(x))`. No indexing or argument-order error. (Had `Ψ₂Sq` been used instead, `IsUnit(a²) ⟺ IsUnit(a)` would even have made it equivalent — but the present choice is the clean one.)
**Attack 2 (logical form: product-unit vs pointwise conjunction).** Loeffler: "P, 2P, 3P ≠ 0 in any fibre". Order 1: an affine point is never the zero section fibrewise — and conversely any section avoiding zero fibrewise factors through the affine chart (set-theoretic avoidance of the `Z=0` point suffices for factoring through the open), so the affine-coordinates format loses no generality. Order 2/3 pointwise at each `p ∈ Spec R`: `ψ₂ ∉ p ∧ ψ₃ ∉ p ⟺ ψ₂ψ₃ ∉ p` (primality), and "∉ every prime ⟺ ∉ every maximal ⟺ unit". So `IsUnit(ψ₂ψ₃) ⟺ (nowhere 2-torsion) ∧ (nowhere 3-torsion)` — exactly "order ∉ {1,2,3} in every fibre". Points of order 6 correctly pass. Equivalent. (Seed's own analysis confirmed.)
**Attack 3 (degenerate characteristics of the dictionary).** `ψ₂ = 0 ⟺ 2P = 0` holds in char 2 too (`ψ₂ = a₁x + a₃`; supersingular char 2 has `a₁ = 0`, and then `a₃` must be a unit else Δ = 0 — consistent with "no 2-torsion"). `Ψ₃` in char 3 supersingular: `b₂ = 0` gives constant `b₈`, and `b₈ = 0` would force Δ = −27b₆² = 0 — again consistent. The order-3 direction does require nonsingularity — supplied by `[W.IsElliptic]` at the use site (E1), not by this def: acceptable, but worth one docstring sentence.
**Attack 4 (spec gap).** The fibrewise dictionary ("in no residue field does P become 0, 2- or 3-torsion") lives only in the docstring; no Lean lemma states `NowhereOrderLEThree ↔ ∀ fibrewise…`. For the ring-level programme this def *is* the working hypothesis (fine), but a pinning spec lemma would close the drift surface permanently.
**Verdict: SURVIVED** (optional: add the dictionary spec lemma; note the `IsElliptic` dependency of the order-3 direction in the docstring).

---

## `exists_unique_variableChange_isTateNormal` (RP:63)

**Attack 1 (point-normalisation encoding).** Is `vc.r = x ∧ vc.t = y` the same as "iso maps (0:0:1) to P"? From the tool-verified action, the image of `(x,y)` is `(u⁻²(x−r), u⁻³(y−t−s(x−r)))`, which is `(0,0)` iff `r = x` and then `t = y`, for every `u, s`. Equivalent — and orientation-compatible with Loeffler (his unique iso `E(α,β) ≅ E` sending `(0:0:1) ↦ P` is the inverse of our `W ≅ vc • W`; unique on one side iff unique on the other, and `vc ↦ induced iso` is injective). (Seed discharged.)
**Attack 2 (∃!-packaging vs "unique α, β … and a unique isomorphism").** `(α,β)` is recovered from `vc` as `((vc•W).a₁, (vc•W).a₂)`, so unique-`vc` ⟺ unique-(α,β)-plus-unique-iso. Also Loeffler's conclusion `Δ(α,β) ∈ Γˣ` is omitted but automatic: `Δ(vc•W) = u⁻¹²Δ(W)` a unit from `[W.IsElliptic]`. Harmless (could add `(vc • W).IsElliptic` to the conclusion for free).
**Attack 3 (scope drift — ring vs scheme).** Loeffler Prop 3.3.4 is for arbitrary `S` (proof glues local Weierstrass equations; "local uniqueness gives global existence"). The Lean statement is over a ring = affine `S` with a chosen global Weierstrass model. This narrowing is deliberate and recorded (decomposition E1 "ring-level restriction"); no statement weakening within that scope. Watch item: when the scheme-level version lands it must *quote this lemma*, not re-prove.
**Attack 4 (edge).** Zero ring: all hypotheses hold vacuously (`IsUnit 0`), `VariableChange 0` is a singleton — ∃! holds trivially. No contradiction.
**Verdict: SURVIVED.**

---

## `tateCurve` (RP:70)

**Attack 1 (coefficients vs Def 3.3.3).** `a₁ = X 0 (= A = α), a₂ = a₃ = X 1 (= B = β), a₄ = a₆ = 0` — matches the display exactly (seed discharged).
**Attack 2 (missing sanity spec).** No lemma `tateCurve.IsTateNormal` (provable by `⟨rfl, rfl, rfl⟩`) — cheap pin, recommended.
**Attack 3 (universe/computability).** `MvPolynomial (Fin 2) ℤ : Type 0`; `noncomputable` justified (Finsupp). Cross-universe use in E2 checked below.
**Verdict: SURVIVED.**

---

## `tateRing` (RP:80)

**Attack 1 (source).** `Localization.Away tateCurve.Δ` = `ℤ[A,B][Δ(A,B)⁻¹]` — matches "Spec ℤ[A, B, Δ(A,B)⁻¹]" (Cor 3.3.5 verbatim, PDF line 1097). `tateCurve.Δ` is mathlib's discriminant of the displayed curve = Loeffler's `Δ(A,B)` by construction — no independent normalisation to drift.
**Attack 2 (universe).** Fixed at `Type 0` while consumers take `A : Type u`: `RingHom` is cross-universe; fine (checked in E2).
**Attack 3 (API).** `IsLocalization.Away.lift` exists for the discharge; `Localization.Away` is the canonical model. No obstruction.
**Verdict: SURVIVED.**

---

## `tateRing_homEquiv` (RP:89)

**Attack 1 (junk-statement risk — `Nonempty (≃)`).** `Nonempty (X ≃ Y)` asserts only *equal cardinality*. The intended content (Cor 3.3.5: the pair *represents* the functor) is that the **canonical** map `φ ↦ (φ(A), φ(B))` is a bijection onto the Δ-unit locus; the statement as written could in principle be discharged by a cardinality argument (e.g. for `A = ℂ` both sides are continuum-sized for reasons unrelated to the universal property), and it carries no naturality in `A`. By the project's own honesty gate (decomposition.md "junk-statement kills"; plan.md "no junk structures that bundle the hard content without a discharge obligation") this under-specifies T-E2. **Fix**: state the canonical equiv — e.g. a `def tateRingHomEquiv : (tateRing →+* A) ≃ {c // …}` (constructed via `MvPolynomial.eval₂Hom` + `IsLocalization.Away.lift`, data real, `sorry` only in the proof obligations) plus a spec lemma `(tateRingHomEquiv φ).1 = (φ (algebraMap _ _ (X 0)), φ (algebraMap _ _ (X 1)))`; or add a naturality clause in `A` in the style of `RelativelyRepresentable`.
**Attack 2 (Δ-map orientation).** RHS condition is `IsUnit ((tateCurve.map (eval₂Hom (Int.castRingHom A) (fun i => if i = 0 then c.1 else c.2))).Δ)`. Via `map_Δ`, this is `IsUnit (Δ(c.1, c.2))` with `X 0 ↦ c.1 = α`, `X 1 ↦ c.2 = β` (`Fin 2`: the else-branch is exactly `i = 1`). Orientation correct (seed discharged).
**Attack 3 (universe).** `(tateRing →+* A) : Type u`, subtype `: Type u`, `≃` fine; `Int.castRingHom A` correct base map. Typechecks (file builds).
**Attack 4 (source completeness).** Loeffler's functor is on *pairs (E, P) up to equivalence*; the docstring honestly scopes this statement to the (α,β)-parametrisation half and defers the pairs-interpretation to T-E1 — no hidden claim.
**Verdict: NEEDS-FIX** — replace `Nonempty (≃)` by a pinned canonical equivalence (or add naturality); as stated it does not force the mathematical content of T-E2.

---

## `EllHom.pullSection` (RP:104)

**Attack 1 (lift plumbing).** `f.isPullback.lift (f.baseHom ≫ P.1) (𝟙 X.base) w` with `w` reducing by `P.2`; result is a `X.base ⟶ X.E` and `lift_snd` gives `· ≫ X.π = 𝟙` — a genuine `Section`. Signature and lemma names verified in mathlib (`Defs.lean:106/116`). The pulled section is the unique one with `top ∘ s' = P ∘ baseHom` — the standard cartesian-square pullback of a point.
**Attack 2 (variance).** `(f : X ⟶ Y) → Y.curve.Section → X.curve.Section` — contravariant, matching presheaf restriction; instantiated in the functors with `f.unop` correctly (obj X → obj Y for `f : X ⟶ Y` in the opposite category — re-derived, correct).
**Attack 3 (style/API).** `R` is an explicit argument (section variable) though inferable from `f` — minor; consider `{R}`. Name `pullSection` vs mathlib-ish `Section.pullback` — cleanup-lane matter only.
**Verdict: SURVIVED.**

---

## `gammaOneNaiveProblem` (RP:113)

**Attack 1 (counterexample — the level predicate is not the source's).** `obj` uses `IsNaiveGammaOne` (`LevelStructure/Basic.lean:52`), which is **purely fibrewise**: `∀ geometric t, (N • P_t = 0 ∧ ∀ 0 < a < N, a • P_t ≠ 0)` — it lacks the **global section-level `(N : ℤ) • P = 0`**. KM 1.4.4 carries the standing hypothesis "Let P ∈ C(S) be a point *killed by N*" (verbatim in decomposition.md D5); Loeffler's own Y₁-construction pins the same: Def 3.3.6 (continued), PDF — "let Y_N be the **closed subscheme** of Y … where `N·(0:0:1) = (0:1:0)`" — the representing scheme *forces* `N•P = 0` as sections. Concrete separation: `S = Spec ℚ̄[ε]`, `E = E₀ ×_ℚ̄ S`, `P = P̃₀ + v` with `P₀` of exact order `N` and `0 ≠ v ∈ Lie E₀` (kernel of `E(ℚ̄[ε]) → E(ℚ̄)`): every geometric point of `S` factors through `Spec ℚ̄`, so `IsNaiveGammaOne` holds, yet `N • P = N v ≠ 0` (`N` invertible). So this functor strictly contains the KM/Loeffler functor and differs from it on non-reduced bases.
**Attack 2 (internal inconsistency).** `IsNaiveFullLevel` (same file, line 43) **does** include the global kill `((N:ℤ) • P = 0 ∧ (N:ℤ) • Q = 0)`; the Γ₁ predicate omits it. The asymmetry has no source justification — evidence of oversight, not design.
**Attack 3 (variance + plumbing).** `map f := ↾fun P => ⟨pullSection R f.unop P.1, sorry⟩` — variance re-derived correct; `↾` necessary (Type-homs are wrappers); the subtype-Prop `sorry` (level preserved under pullback) is provable *only because* `EllHom` has `zero_w` (translations would break it) — another cross-confirmation of the `zero_w` decision. `map_id/map_comp` routine ext.
**Attack 4 (base-generality drift, minor).** The source defines the problem on `Ell/ℤ[1/N]` / "category of ℤ[1/N]-schemes"; the Lean def is over any `R` (invertibility appears only in the theorems). Harmless as a definition, but in bad characteristics it is *not* the moduli problem anyone names Γ₁-naive — worth a docstring caveat (the supersingular caution is already quoted).
**Verdict: NEEDS-FIX** — add `((N : ℤ) • P = 0) ∧` to `IsNaiveGammaOne` (mirroring `IsNaiveFullLevel`), or intersect it into this functor's `obj`. As currently written the functor is not KM's/Loeffler's, and the representability theorem below is false for it.

---

## `gammaFullNaiveProblem` (RP:122)

**Attack 1 (source fidelity).** Loeffler Fact 3.8.1 (PDF, incl. continuation): `P_H(E/k̄) = {H-orbits of isomorphisms (ℤ/N)² ≅ E[N]}`; for `H = 1`: "pairs of sections P, Q ∈ E[S] generating E[N] in every fibre". `IsNaiveFullLevel` = (global kill of both) ∧ (every fibrewise N-torsion point ∈ `AddSubgroup.closure {P_t, Q_t}`) — the global kill is justified by Loeffler's own 3.8.2 construction (open subscheme of `E[N] ×_S E[N]`, whose S-points are sections *of E[N]*). Faithful; and over non-reduced bases fibrewise-distinct sections of the étale `E[N]` are automatically disjoint (equalizer open and closed), so with the kill included the naive functor is the right one for `N` invertible.
**Attack 2 (H-orbits vs ordered pairs).** `H = {1}` orbits = ordered pairs; no Weil-pairing/determinant normalisation appears in the source for `P_{Γ(N)}` itself (pairings only enter 3.8.2's representing-scheme description and the `ζ`-variants) — correctly absent here.
**Attack 3 (encoding edge).** `closure {P_t, Q_t}` — integral spans, `Point` group via `pointAddCommGroup` — the intended "generated by P, Q"; degenerate `P_t = Q_t` handled by set-notation (closure of a possibly-singleton) — semantically right (such pairs simply fail generation when `N > 1`… and for `N = 1` everything degenerates consistently: closure ∋ 0 and all N-torsion = 0).
**Attack 4 (base-generality drift).** Same as Γ₁ Attack 4 (defined over any `R`, source only over `ℤ[1/N]`) — same minor caveat.
**Verdict: SURVIVED.**

---

## `gammaOneNaive_representable` (RP:134)

**Attack 1 (counterexample — the conjunction is false as stated).** Take `R = ℚ`, `N = 5`. As shown above, `gammaOneNaiveProblem ℚ 5` evaluated at Artin-local objects `(Spec A, E_A)` at a `ℚ̄`-point `(E₀, P₀)` is pro-represented by `ℚ̄[[t, s]]`: the deformation of `E₀` (one parameter, unobstructed) **times** the *unconstrained* lift of `P₀` (a trivialised torsor under `Ê(𝔪_A)` — trivialised by the canonical étale torsion lift, which the fibrewise-only predicate does not select). Aut(E₀, P₀) is trivial (`N ≥ 4` rigidity), so if some `X` represents the problem, `O^_{X.base, y} ≅ ℚ̄[[t,s]]` at every induced closed point — tangent dimension 2. But field-valued values are finite per curve (≤ #E[5] = 25), so closed points of `X.base` are quasi-finite over the j-line. If additionally `Smooth X.structMap` (the second conjunct), `X.base` is locally of finite presentation and regular; a finite-type ℚ-scheme with 2-dimensional local rings along a locus quasi-finite over `𝔸¹_j` is impossible (any 2-dimensional irreducible component maps to the j-line with some infinite fibre, contradicting the 25-point bound). So `Representable ∧ (∀ X, … → Smooth …)` is **false**. Root cause: the missing `N • P = 0` (previous block); with the kill added, the torsion lift is unique (étaleness) and the functor is the classical `Y₁(N)_R`, for which the statement is the standard theorem.
**Attack 2 (source drift check for the *fixed* statement).** Thm 3.4.4 verbatim covers smoothness over `ℤ[1/N]`; general `R` with `N` invertible follows by base change (Smooth, IsAffineHom stable) — a mild, mathematically-justified generalisation; recommend a docstring sentence noting the base-change step. **Affineness has no verbatim quote**: 3.3.6 gives `Spec` explicitly only for `N = 5`; general `Y₁(N)` is (an open piece of a closed subscheme of) `Spec ℤ[A,B,Δ⁻¹]` and its affineness is a "by construction/standard" fact (KM: affine over the j-line) — flagged QUOTE-PARTIAL.
**Attack 3 (representing-object quantification).** "∀ X, Nonempty (RepresentableBy X) → Smooth ∧ IsAffineHom": representing objects are unique up to Ell/R-iso, and iso in `EllObj` transports `structMap` along a base iso compatible with `base_w`; `Smooth`/`IsAffineHom` are iso-invariant classes — the ∀-form is sound and actually the cleanest formalisation of "the representing scheme is smooth affine". Both classes hover-verified as the intended morphism properties.
**Attack 4 (hypotheses).** `[NeZero N]` is redundant given `4 ≤ N` but required as an instance for elaboration — acceptable pattern. `IsUnit (N : R)` is the right invertibility form.
**Verdict: REJECTED** (as stated, false — inherits the `IsNaiveGammaOne` kill-omission; concrete `ℚ̄[ε]` counterexample + tangent/quasi-finiteness contradiction). **Fix**: add the global kill to `IsNaiveGammaOne` (then the statement is Loeffler 3.4.4 + construction, and survives); also note the base-change generalisation and the affine-part quote gap in the docstring.

---

## `gammaFullNaive_representable` (RP:145)

**Attack 1 (docstring/statement mismatch).** The docstring asserts "the representing scheme `Y(N)` is smooth and affine over `Spec R`", but the theorem states only `Rigid ∧ Representable` — the smooth/affine conjunct present in the Γ₁ analogue is **missing from the formal statement**. Either add the `∀ X, Nonempty (RepresentableBy X) → Smooth ∧ IsAffineHom` conjunct (per Loeffler post-3.8.3: "One can check that `Y_{P_H}` is smooth over ℤ[1/N]") or cut the docstring claim. As-is it's a target-drift trap for the worker.
**Attack 2 (rigidity beyond the quoted base).** Loeffler Prop 3.8.3 verbatim (PDF line 1542) asserts the rigidity criterion **"on Ell/R[1/6]"** only, and his proof sketch handles char 0 and char ≥ 5. The Lean statement claims `Rigid` for any `R` with only `N` invertible (`N ≥ 3`), e.g. `Γ(3)` over `𝔽₂`-algebras — **stronger than the quoted source**. The claim is true and is covered by the GME chain already transcribed (decomposition-gme2.md, B9/Aut computation: "ε ∈ Aut(E,φ), n ≥ 3 invertible ⟹ ε = 1", valid in all characteristics via the Hasse/trace bound in the quaternionic case; = KM 2.7.x/5.1 territory), but the *docstring cites only 3.8.3* — re-point the rigidity citation at the GME 2.6.4 chain and add the KM locator to the PENDING list. Without that, the statement fails the verbatim-quote gate for chars 2,3.
**Attack 3 (functor correctness).** Unlike Γ₁, the underlying predicate has the global kill, so the Artin-local analysis gives the *étale-rigidified* one-parameter deformation theory — no analogue of the Γ₁ counterexample; representability over `ℤ[1/N]` (KM; GME Thm 2.6.8 chain Y in decomposition-gme2.md) base-changes to `R`. First conjunct order (`Rigid ∧ Representable`) also matches the proof logic (rigidity is an input via 3.7.4).
**Attack 4 (hypotheses).** `3 ≤ N` matches "no −1, no elliptic elements for N ≥ 3" (for `N ≤ 2`, `−1` fixes every naive structure — rigidity genuinely fails, so the bound is sharp); `[NeZero N]` redundant-but-required as above.
**Verdict: NEEDS-FIX** (align statement with docstring on smooth+affine — preferably add the conjunct; re-source the any-characteristic rigidity to the GME B9 chain and log the KM quote gap). Mathematical content otherwise supported.

---

# Summary table

| # | Declaration (file:line) | Verdict | Key finding |
|---|---|---|---|
| 1 | `EllObj` (EC:38) | SURVIVED | group-datum enrichment = design D5; category insensitive to it |
| 2 | `EllHom` (EC:50) | SURVIVED | `IsPullback` order correct; `zero_w` NOT automatic (translation cex), NOT in Loeffler-literal (ellipsis = diagram only), but forced by 3.7.3/3.7.4 + functoriality — keep; document + KM-reconcile |
| 3 | `Category (EllObj R)` (EC:61) | SURVIVED | sorries dischargeable: `of_horiz_isIso`, `paste_horiz`, ext |
| 4 | `ModuliProblem` (EC:82) | SURVIVED | universes check out |
| 5 | `EllObj.pullbackAlong` (EC:88) | SURVIVED | — |
| 6 | `EllObj.pullbackAlongMap` (EC:96) | SURVIVED | direction correct for contravariant restriction; `of_right` closes the sorry |
| 7 | `Representable` (EC:107) | SURVIVED | duplicates mathlib `Functor.IsRepresentable` — dedup |
| 8 | `RelativelyRepresentable` (EC:114) | SURVIVED | naturality clause = full Over-naturality; direction verified |
| 9 | `Rigid` (EC:126) | SURVIVED | quantified isos = Aut(E/S) exactly (needs `zero_w`); free-action encoding sound |
| 10 | `representable_iff` (EC:135) | SURVIVED | sanity sweep passes; KM 4.7 quote pending |
| 11 | `IsTateNormal` (RP:44) | SURVIVED | coefficients match Def 3.3.3 exactly |
| 12 | `NowhereOrderLEThree` (RP:53) | SURVIVED | `Ψ 2` = y-involving ψ₂; `evalEval x y` order correct; dictionary robust in char 2,3; product-unit ⟺ pointwise conditions |
| 13 | `exists_unique_variableChange_isTateNormal` (RP:63) | SURVIVED | `(r,t)=(x,y) ⟺ P ↦ (0,0)` verified from the SMul action; ring-level scope documented |
| 14 | `tateCurve` (RP:70) | SURVIVED | add trivial `IsTateNormal` spec lemma |
| 15 | `tateRing` (RP:80) | SURVIVED | — |
| 16 | `tateRing_homEquiv` (RP:89) | **NEEDS-FIX** | `Nonempty (≃)` is cardinality-only (junk risk); pin the canonical map or add naturality |
| 17 | `EllHom.pullSection` (RP:104) | SURVIVED | `lift`/`lift_snd` usage verified |
| 18 | `gammaOneNaiveProblem` (RP:113) | **NEEDS-FIX** | `IsNaiveGammaOne` lacks global `(N:ℤ)•P = 0` (KM 1.4.4 standing hyp; Loeffler's closed-subscheme construction); inconsistent with `IsNaiveFullLevel` |
| 19 | `gammaFullNaiveProblem` (RP:122) | SURVIVED | kill conjunct present; faithful to 3.8.1/3.8.2 |
| 20 | `gammaOneNaive_representable` (RP:134) | **REJECTED** | false as stated: `ℚ̄[ε]` counterexample ⟹ pro-representation `ℚ̄[[t,s]]` (tangent dim 2) vs quasi-finite over j + Smooth conjunct — contradiction; fixed by #18's repair |
| 21 | `gammaFullNaive_representable` (RP:145) | **NEEDS-FIX** | statement omits the docstring's smooth+affine conjunct; rigidity claim exceeds the 3.8.3 quote (re-source to GME B9 "n ≥ 3 invertible") |

**Collateral (out-of-scope files, same root cause as #18/#20)**: the missing-kill counterexample also falsifies the ⟸ directions of `isGammaOne_iff_naive` (`LevelStructure/Basic.lean:86`) and `Section.hasExactOrder_iff_geometric` (`LevelStructure/ExactOrder.lean:81`) as currently stated (Drinfeld exact order ⟹ killed by N by KM 1.4.2, but the fibrewise RHSs don't imply killed). This *confirms* the "attack pending" already recorded at decomposition.md leaf D5 — it fires; the same one-line fix (add `(N:ℤ)•P = 0` to the naive form) repairs all four statements.

# QUOTE-MISSING list

1. **KM 4.1** (morphism convention of Ell, incl. zero-section compatibility) — KM Ch. 4 not in `refs/`; Loeffler's display has no zero clause (ellipsis resolved from the PDF). `zero_w` adjudicated necessary; verbatim reconciliation outstanding.
2. **KM 4.2 / 4.3 / 4.4** locators for `RelativelyRepresentable` / `Representable` / `Rigid` — covered by Loeffler 3.7.1/3.7.3 verbatim; KM reconciliation pending (already flagged at E0).
3. **KM 4.7** for `representable_iff` — Loeffler 3.7.4 verbatim in hand; KM pending (already flagged at E4).
4. **Rigidity of `[Γ(N)]` for `N ≥ 3` in residue characteristics 2, 3** (`gammaFullNaive_representable`): Loeffler 3.8.3 covers only `Ell/R[1/6]`; the GME 2.6.4 Aut-computation quote (decomposition-gme2.md, chain B9) covers "n ≥ 3 invertible"; the KM verbatim (2.7.x/5.1) is missing — docstring currently cites only 3.8.3.
5. **Affineness of `Y₁(N)` for general `N`** (second conjunct of `gammaOneNaive_representable`): Thm 3.4.4 quotes smoothness only; `Spec`-affineness is verbatim only for `N = 5` (Def 3.3.6); general-`N` affineness is construction/standard (KM affine-over-j-line) — needs a locator when the KM text lands.
6. *(No gap)* Loeffler 3.8.2's étaleness of relative representability is deliberately not claimed in the Lean `RelativelyRepresentable` — no obligation.

# Priority fixes

1. **Add `((N : ℤ) • P = 0) ∧` to `IsNaiveGammaOne`** (`LevelStructure/Basic.lean:52`) — un-rejects #20, repairs #18 and the two collateral iffs; mirrors `IsNaiveFullLevel`.
2. **Re-state `tateRing_homEquiv`** with a pinned canonical equivalence (def + apply-spec, or naturality clause).
3. **`gammaFullNaive_representable`**: add the smooth/affine conjunct (or amend the docstring); re-cite rigidity to GME 2.6.4/B9 alongside 3.8.3.
4. **`EllHom` docstring**: record that `zero_w` is an explicit disambiguation (not in Loeffler's display; forced by functoriality of the level problems and by 3.7.3/3.7.4), plus KM-4.1 reconciliation flag.
5. Minor: use `Functor.IsRepresentable` for `Representable`; add `tateCurve` `IsTateNormal`/ellipticity spec lemmas; consider the fibrewise dictionary spec for `NowhereOrderLEThree`.