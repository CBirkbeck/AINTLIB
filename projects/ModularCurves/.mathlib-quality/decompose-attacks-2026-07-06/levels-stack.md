<!-- Adversarial /develop --decompose attack log, agent a88063f6a3a777126, archived 2026-07-06 -->

All evidence is gathered (files read in full, supporting definitions traced, mathlib conventions verified against the workspace's mathlib: `Matrix.mul_apply`/`mulVec` row-col convention, `GeneralLinearGroup = (Matrix n n R)ˣ`, `SpecialLinearGroup.map`/`.toGL`, `IsOfFinOrder` all confirmed present). Here is the red-team report.

---

# Adversarial verification — `Moduli/{Groupoid,GammaH,Coarse,Stack}.lean` (post DEF-1/2/3)

**Method.** Every public declaration attacked in ≥3 of five categories: **[FALSITY]** truth/counterexample, **[HYP]** hypothesis strength & degenerate cases, **[SRC]** fidelity to the quoted sources, **[TYPE]** types/universes/conventions/elaboration, **[DEP]** provability of the sorries & hidden dependencies. Files audited at `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves/projects/ModularCurves/ModularCurves/Moduli/`.

**Headline findings (new, not covered by DEF-1/2/3):**
1. **`glSmul_mul` is FALSE** — asserts the left-action law for what is arithmetically a right action (precomposition). Confirmed by explicit computation against mathlib's `Matrix.mul_apply`.
2. **`isIso_homOver` (T-G1) is FALSE** — `[2] : E ⟶ E` is a `HomOver` of degree 4. `HomOver` omits the cartesian/iso condition that `EllHom` has; the "groupoid" claims are systematically wrong (`HomOver`, `LevelledHom`, `fullLevelGroupoid`, `GammaHClasses` all infected).
3. **`aut_trivial_of_fullLevel` (T-G3) is FALSE as stated** — `f = [1+N]` is a non-identity pointed endo fixing every full level structure. GME 2.6.4 needs `deg ε = 1` (ε ∈ Aut); the endo form is unsalvageable.
4. **`gammaFullDrinfeld_representable` (T-H8) and `gammaOneDrinfeld_representable` (T-H9) are FALSE as stated** over arbitrary `R`: degenerate Drinfeld structures in char p | N (KM Caution 1.4.3's own in-hand example) are fixed by `[-1]`, killing rigidity, hence representability. GME's own quoted over-ℤ condition ("coprime m, n ≥ 3", decomposition-gme2 §B9/Y.6) contradicts the bare `N ≥ 3`/`N ≥ 4` forms.
5. **`exists_coarse_gammaH` is junk as stated** — `Nonempty(≃)` with an unconstrained `∃ Y` is a pure cardinality claim, satisfiable by `𝔸¹_R`; and `GammaHClasses` collapses non-isomorphic isogenous curves (via non-iso `HomOver`s).
6. **Hidden dependency**: every moduli-functor `map`-sorry (`gammaHNaiveProblem`, both Drinfeld problems) silently needs group-law-uniqueness/rigidity (A6.δ/T-G2) to make `pullSection` additive — contradicting the plan amendment "nothing in streams B/C/D/E depends on [the canonicity project] anymore".

---

## Groupoid.lean

### `EllipticCurve.HomOver` (Groupoid.lean:34–38)
**Attacks:**
- **[FALSITY/role]** The structure admits non-invertible morphisms: for any `E`, `⟨E.mulByHom 2, mulByHom_π 2, zero-preservation⟩` is a `HomOver E E` (degree 4 on fibres), and the zero morphism `⟨E.π ≫ E'.zero, …⟩` is a `HomOver E E'` between *any* two curves. So `HomOver` is "pointed S-morphism", **not** the morphism notion of the moduli groupoid. Loeffler Def 3.7.1's morphisms are cartesian squares (`E ≅ E' ×_T S`); the same-base specialisation forces iso — `HomOver` dropped exactly the `isPullback` field that `EllHom` (EllCategory.lean:50–57) has.
- **[SRC]** Docstring "(automatically a homomorphism — rigidity; T-G2)" is true for pointed morphisms (abelian-scheme rigidity), but the file's *groupoid* framing (line 41–42 "every morphism is an isomorphism (T-G1)") conflates rigidity (hom-ness) with invertibility; no source supports the latter.
- **[TYPE]** `@[ext]` present ✓ — `HomOver.ext` reduces morphism equality to `hom`-equality (Prop fields proof-irrelevant); this is what makes the category laws below provable.
- **[DEP]** Downstream `Coarse.GammaHClasses` and the T-G3 statement consume `HomOver` as if iso-closed — both break (see below).
**Verdict:** definition well-formed, **role-defective**: add `IsIso hom` (or an iso-based wrapper) wherever "groupoid/Aut" semantics is intended; as-is it silently changes ≥3 downstream statements.

### `instance : Category (EllipticCurve S)` (Groupoid.lean:43–50)
**Attacks:**
- **[DEP]** Seed premise "axioms sorried" is wrong for this file: `id_comp/comp_id/assoc` are real `intros; ext; simp` proofs (lines 48–50), enabled by `@[ext]`; data (`id`, `comp`) real with real coherence rewrites. No sorries here.
- **[FALSITY]** Laws are true and the proofs are the standard ones; `comp` associativity reduces to `Category.assoc` in `Scheme` ✓.
- **[SRC/TYPE]** The docstring (41–42) claims this is "the groupoid of elliptic curves over S — the value at S of the moduli stack": false as a category-level claim (contains `[2]`, zero maps). The *core* of this category is the stack's value. Docstring must be corrected or the Hom changed; the `Category` instance itself is fine.
**Verdict:** **sound as a category**; docstring/role claim wrong (inherits the `HomOver` defect).

### `isIso_homOver` (T-G1) (Groupoid.lean:55)
**Attacks:**
- **[FALSITY]** **FALSE.** Counterexample: any nonempty `S`, any `E`, `f := ⟨E.mulByHom 2, E.mulByHom_π 2, h₀⟩` (`h₀ : E.zero ≫ [2] = E.zero` holds — group-object power of the unit). An iso in this category is an iso of total spaces; `[2]` has fibre degree 4 (B1/`torsion_rank`), not 1. Only over `S = ∅` is the statement vacuously fine.
- **[SRC]** Cited "KM 2.4-adjacent, ⧗KM" — no verbatim quote exists (and none can: KM 2.4 is rigidity = homomorphism-ness, not invertibility). QUOTE-MISSING and irreparably so.
- **[DEP]** T-G3's endo-form, `GammaHClasses`' docstring, and GammaH.lean:221 ("discrete on isomorphism classes") all cite T-G1 as their justification; all collapse with it.
- **[HYP]** No hypothesis can rescue it except changing `Hom` (restrict to cartesian/iso morphisms), after which it becomes definitional.
**Verdict:** **FALSE — must be deleted or restated** (e.g. "a `HomOver` whose underlying morphism is an iso of schemes iff …", or redefine `Hom` with `isPullback` as in `EllHom` and make T-G1 trivial).

### `IsoClasses` (Groupoid.lean:61–64)
**Attacks:**
- **[FALSITY]** The seed's worry (≅ in *this* category) is benign: isos in the pointed-morphism category are exactly pointed `S`-isos, the correct relation — even though the ambient category is not a groupoid. The `Setoid`'s `iseqv` is *proved inline* (`Iso.refl/symm/trans`), not sorried ✓.
- **[TYPE]** `Type (u+1)` correct (`EllipticCurve S : Type (u+1)`); `Quotient` of an inline anonymous-constructor `Setoid` is awkward for later `Quotient.lift` work (no named `Setoid` instance) — style note only.
- **[HYP]** Over `S = ∅` there is exactly one curve up to iso (the empty one) — degenerate but harmless for the j-line consumer (alg-closed points only).
**Verdict:** **sound**.

### `aut_trivial_of_fullLevel` (T-G3) (Groupoid.lean:71–75)
**Attacks:**
- **[FALSITY]** **FALSE as stated.** `f := ⟨E.mulByHom (1+N), …⟩ : E ⟶ E` satisfies `hP`/`hQ`: `P.1 ≫ [1+N] = ((1+N)•P).1 = (P + N•P).1 = P.1` (via `point_smul_eq_comp_mulBy`, T-A6d, and `(N:ℤ)•P = 0` from `hPQ.1.1`), likewise `Q`; but `f ≠ 𝟙 E` over any nonempty `S` (degree `(1+N)² > 1`). All hypotheses (`3 ≤ N`, `NIsInvertible`) are satisfied — the counterexample is hypothesis-proof. The seed's defense ("endo OK, consistent with T-G1") fails because T-G1 is itself false.
- **[SRC]** GME p. 151 (decomposition-gme2 §B9, quote in hand): "`ε ∈ Aut(E,φ)`, n ≥ 3 invertible: … `1 = deg ε = 1 + nTr(g) + n²deg g`". The proof *consumes* `deg ε = 1`, i.e. ε invertible. The Lean statement deviates from the quote exactly at the point that makes it false. Fix: `(f : E ≅ E) (hP : P.1 ≫ f.hom.hom = P.1) … → f = Iso.refl E`, or add `[IsIso f]`.
- **[HYP]** With the iso fix, hypotheses match GME p. 151 precisely: `hN : 3 ≤ N` ✓, `hinv : NIsInvertible S N` = `IsUnit (N : Γ(S,⊤))` = "n invertible on S" ✓ (unit in global sections ⟺ unit in every stalk ⟺ invertible on S — right formalisation). Note the fixed statement is over arbitrary (possibly non-reduced) `S`; still true — GME's Tr/deg argument is over a base, and pointed infinitesimal automorphisms vanish (`H⁰(T_E(-0)) = 0`) — but the fibrewise-to-`S` step is real proof content, not free.
- **[TYPE]** `P Q : E.Section` with `hPQ` binding them to a *naive* structure ✓ (right register: rigidity is a naive/invertible-N statement); `hP : P.1 ≫ f.hom = P.1` is the correct "f(P) = P" orientation ✓.
**Verdict:** **FALSE as stated; true and correctly-hypothesised after replacing the endo by an iso.** High priority: `levelledCurve_descent_of_torsor`'s proof route needs the fixed version.

---

## GammaH.lean

### `FullLevelPt` (GammaH.lean:54–55)
**Attacks:**
- **[SRC]** Bundles the *naive* structure only (docstring says so ✓); name doesn't say "naive" while the ambient convention (`gammaFullNaiveProblem` vs `…Drinfeld…`) does — rename to `NaiveFullLevelPt` or accept the local convention (levelled groupoid is a naive-register object by design D6 ✓).
- **[TYPE]** `Type u` subtype of `Section × Section` ✓; `[NeZero N]` needed by `IsNaiveFullLevel` ✓.
- **[HYP]** For `N = 1` the type is the singleton `{(0,0)}` (killed-by-1 forces `P = Q = 0`); consumers (e.g. not-rigid at `N ≤ 2`) rely on this — checked, consistent.
**Verdict:** **sound**.

### `glSmul` (GammaH.lean:64–70)
**Attacks:**
- **[TYPE/convention — the seed's index audit]** File: `g•L = ((m 0 0)•P + (m 1 0)•Q, (m 0 1)•P + (m 1 1)•Q)`. Honest math: with `φ(e₁) = P, φ(e₂) = Q` and mathlib's column-vector action (`mulVec M v i = ∑ j, M i j * v j`, verified in `Mathlib/Data/Matrix/Mul.lean:698`), `g·e₁` = first *column* = `(g 0 0, g 1 0)`, so `(φ∘g)(e₁) = (g 0 0)•P + (g 1 0)•Q`. **The file matches** — first component ✓, second component = `(φ∘g)(e₂)` ✓. Docstring formula `(g₁₁P + g₂₁Q, g₁₂P + g₂₂Q)` (1-indexed) also matches the code ✓. **No index transpose; `glSmul g L` is genuinely `L ∘ g` = right multiplication `vecMul L g`.** (This is what convicts `glSmul_mul` below.)
- **[DEP]** Membership sorry (T-H2): TRUE — killed-by-N: `N•(aP + cQ) = 0` ✓; fibre generation: `g ∈ GL₂` invertible mod N re-expresses `P,Q` from the new pair modulo N-torsion ✓ (invertibility is genuinely used — the def would be false for a mere matrix monoid action).
- **[TYPE]** `let m : Matrix … := g` uses the `Units.val` coercion (`GeneralLinearGroup` is an abbrev for `(Matrix n n R)ˣ`, verified) ✓; `ZMod.val`-lifts are well-defined on the subtype *only because* level points are killed by N (docstring says so ✓); edge `N = 1`: `(1 : ZMod 1).val = 0` makes `glSmul 1 L = ((0:ℤ)•P + …)` — still equals `L` since `P = Q = 0`; fine but any `glSmul_one` proof must not assume `(1 : ZMod N).val = 1`.
**Verdict:** **sound** (formula correct for precomposition; membership sorry true).

### `glSmul_mul` (T-H2a) (GammaH.lean:74–76)
**Attacks:**
- **[FALSITY]** **FALSE — the high-value target confirmed.** `glSmul m L = vecMul L m`, so `glSmul h (glSmul g L) = vecMul L (g*h) = glSmul (g*h) L`; the file asserts `glSmul (g*h) L = glSmul g (glSmul h L) = glSmul (h*g) L`, i.e. `glSmul (g*h) L = glSmul (h*g) L` for all `g,h,L`. Concrete refutation: `S = Spec ℂ`, `E` any elliptic curve, `L` an honest basis of `E[N](ℂ)` (exists for every `N ≥ 2`), `g = (1 1; 0 1)`, `h = (1 0; 1 1)`: `g*h = (2 1; 1 1)`, `h*g = (1 1; 1 2)` differ mod N for all `N ≥ 2`, and `vecMul L (–)` is injective mod N on a basis. Explicit first components: LHS `(g*h)` gives `2P+Q`... vs RHS composite gives `(Aa+Cb)P + …` = the `h*g` entry — unequal. (Verified against `Matrix.mul_apply : (M*N) i k = ∑ j, M i j * N j k`.) The `ZMod.val`-lift slack (docstring's "compose correctly mod N") is real but only fixes mod-N discrepancies — it cannot repair a transposed group law.
- **[SRC]** Precomposition is a **right** action: `(φ∘g)∘h = φ∘(g*h)`. No source states the left law; Loeffler 3.8.1 only needs orbits. Correct statement: `glSmul (g * h) L = glSmul h (glSmul g L)` (or define `glSmul` via `g⁻¹` to get a left action — then the membership proof changes too).
- **[DEP]** Any worker "discharging" `hOrbitSetoid.iseqv`, `gammaHNaive_bot`, or T-H3 by citing `glSmul_mul` as stated is building on a false lemma; the sorry is undischargeable as written, so the pipeline would stall here rather than corrupt — but the board should not carry a false leaf.
**Verdict:** **FALSE — flip the composition order (right-action law) or invert the action.**

### `hOrbitSetoid` (GammaH.lean:79–82)
**Attacks:**
- **[FALSITY]** The *relation* `∃ g ∈ H, glSmul g L = L'` is a genuine equivalence despite the `glSmul_mul` fiasco: refl via `g = 1` (`glSmul_one`, true incl. `N = 1` edge); symm via `g⁻¹` (works under either composition convention since `g*g⁻¹ = g⁻¹*g = 1`); trans via `g * g'` **in the corrected order** (`glSmul g' (glSmul g L) = glSmul (g*g') L`), and `H` subgroup closes ✓. Right-orbits `L·H` = left-orbits as partitions ✓ matches Loeffler's "H-orbits".
- **[DEP]** `iseqv` sorried — fine as a Prop-sorry, but its discharge depends on the *corrected* T-H2a; note on the ticket.
- **[TYPE]** Anonymous-constructor `Setoid` with a sorried `iseqv` field: legal; `Quotient` over it in `gammaHNaiveProblem` typechecks ✓.
**Verdict:** **sound** (with the discharge-path caveat).

### `FullLevelPt.pullAlong` (GammaH.lean:86–93)
**Attacks:**
- **[DEP]** Membership sorry (T-H2b) TRUE and — unlike the functor sorries below — **provable without rigidity**: `E.baseChange σ` carries the *canonical* pullback group structure (`Over.grpObjMkPullbackSnd`, GroupLaw.lean:135–146), for which `Point.asSection` is additive by construction; killed-by-N and geometric-fibre generation transfer along `t' → T' → T` ✓.
- **[TYPE]** The two `Point.asSection E σ ⟨σ ≫ L.1.1.1, …⟩` terms typecheck (`Point.pull` then `asSection`; the rewrites match `Point.pull`'s proof shape) ✓.
- **[HYP]** No compatibility lemma `pullAlong_id`/`pullAlong_comp`/`pullAlong_glSmul` is stated anywhere — `levelledCurve_descent_of_torsor` and T-H3 will need them; unstated spec gap.
**Verdict:** **sound**; add the functoriality/equivariance specs to the board.

### `gammaHNaiveProblem` (T-H3 carrier) (GammaH.lean:107–115)
**Attacks:**
- **[DEP — the seed's equivariance question, adjudicated]** The `Quotient.map` respect-sorry needs: `glSmul g L = L' ⟹ ∃ g' ∈ H, glSmul g' (pull L) = pull L'`, with witness `g' = g`, which requires `pullSection (a•P + b•Q) = a•pullSection P + b•pullSection Q`. `EllHom` (EllCategory.lean:50–57) has **no group-compatibility field**, and `X.curve.grp` is an independent datum — additivity of `pullSection` is TRUE only because a pointed iso onto the pullback is automatically a group iso, i.e. **uniqueness of the group law with given identity (A6.δ / `grpObj_unique`) or rigidity (T-G2)**. This is a **hidden dependency on the deferred canonicity project**, contradicting decomposition.md's amendment "nothing in streams B/C/D/E depends on it anymore". Must be surfaced: state `EllHom.pullSection_add` (sorried spec) and add the board edge.
- **[FALSITY]** With that theorem, the functor is mathematically correct (membership: `H`-orbit data pulls back; `map_id/map_comp`: `pullSection` functoriality is pure pullback-lift uniqueness, no rigidity needed ✓).
- **[SRC]** Loeffler Fact 3.8.1 quoted ✓; specialisation table (⊥, `Γ₁`, Borel) matches; KM Ch. 3/7 locators pending (recorded ✓).
- **[TYPE]** `↾Quotient.map f h` as a `Type u`-morphism ✓; `Quotient` of `hOrbitSetoid` at each object ✓.
**Verdict:** **sound modulo the flagged hidden dependency** (must be put on the board; it is not free).

### `gammaHNaive_bot` (T-H1) (GammaH.lean:119–120)
**Attacks:**
- **[FALSITY]** TRUE: `⊥`-orbits are singletons — `glSmul 1 L = L` (incl. `N = 1` degenerate-val edge, where `P = Q = 0`), so the quotient is the subtype, naturally in `X` (both sides pull back by `pullSection` componentwise).
- **[TYPE]** `≅` in the functor category `(EllObj R)ᵒᵖ ⥤ Type u` wrapped in `Nonempty` — avoids choice of the iso; fine.
- **[DEP]** Discharge needs `glSmul_one` — do not derive it from `(1 : ZMod N).val = 1` (fails at `N = 1`); derive from the group structure (`0 • Q = 0`, `1 • P = P`).
**Verdict:** **sound**.

### `gammaHNaive_relativelyRepresentable` (T-H4) (GammaH.lean:127–130)
**Attacks:**
- **[SRC]** Loeffler 3.8.2 (quoted verbatim in the module docstring) says "relatively representable **and étale**… finite étale". The Lean statement asserts only `RelativelyRepresentable` — the finite-étale half is silently dropped (docstring line 124 still promises it). Statement-vs-docstring drift; per the faithfulness constraints, either strengthen `RelativelyRepresentable`'s use here with a conjunct (`IsFinite`/`IsEtale` of the representing `f : Z ⟶ X.base`) or state a companion theorem.
- **[HYP]** `hinv : IsUnit (N : R)` matches "over Ell/ℤ[1/N]" ✓ (unit in `R` ⟹ invertible on every `R`-scheme). Without étaleness in the conclusion the statement is plausibly true even without `hinv` (Drinfeld-style finiteness) — hypothesis not wrong, just tied to the dropped conjunct.
- **[FALSITY]** As stated: TRUE (weak form of Loeffler 3.8.2; proof route via Weil-pairing open locus + `H`-quotient consumes streams C and Q as recorded).
**Verdict:** **true but under-stated relative to its own docstring/source** — fidelity fix needed.

### `gammaHNaive_rigid_iff` (T-H5) (GammaH.lean:136–143)
**Attacks:**
- **[FALSITY — degenerate ring]** **FALSE for `R = 0`** (the zero ring): `IsUnit ((6N : ℕ) : 0)` holds, every `EllObj` has empty base, so `Rigid` is vacuously true; but the RHS fails for e.g. `H = ⊤, N = 3, γ = -1` (`IsOfFinOrder (-1)`, image `-1 ∈ ⊤`, `-1 ≠ 1`). Needs `Nontrivial R` — note DEF-1 added exactly the analogous guard (`hR : ∃ X, Nonempty X.base`) to T-H7 but this statement was not given one. For `R ≠ 0` the ⟸/⟹ witnesses exist (residue field → k̄ → curves with j = 0/1728 and chosen bases), matching the source.
- **[SRC — the −1 and H∩SL₂ checks, adjudicated]** (i) `H` vs `H ∩ SL₂(ℤ/N)`: the reduction of `SL₂(ℤ)` lands in `SL₂(ℤ/N)` automatically (det is preserved by `SpecialLinearGroup.map`), so `{γ : image ∈ H}` = Loeffler's preimage of `H ∩ SL₂(ℤ/N)` — **equivalent** ✓. (ii) "contains no elements of finite order": literally read this excludes `1` (which is always in the preimage); the Lean form `IsOfFinOrder γ → γ = 1` is the correct "torsion-free" reading ✓. (iii) `−1`-case consistency: for `N ≤ 2`, `-1 ↦ 1 ∈ H` always, so RHS is false for every `H` — consistent with T-H7 (never rigid at `N ≤ 2`) ✓; for `N ≥ 3`, RHS bans `−1 ∈ H̄` exactly per the source ✓.
- **[HYP]** `IsUnit ((6 * N : ℕ) : R)`: `Nat.cast` of the product; equivalent to `IsUnit 6 ∧ IsUnit N` ✓ = Loeffler's `R[1/6]` (rigidity criterion) + the `ℤ[1/N]` home of `P_H` — faithful. Cosmetic: `(6 * N : ℕ)` cast is fine but a `simp`-unfriendly form; consider `IsUnit (6 * N : R)` with a `push_cast` bridge.
- **[TYPE]** `Matrix.SpecialLinearGroup.toGL` and `.map` verified present in mathlib (GeneralLinearGroup/Defs.lean:256; SpecialLinearGroup.lean:225); `Int.castRingHom (ZMod N)` ✓; membership in `Subgroup (GL (Fin 2) (ZMod N))` typechecks ✓. `IsOfFinOrder` on `SpecialLinearGroup (Fin 2) ℤ` ✓ (group instance exists).
**Verdict:** **needs `Nontrivial R` (or a nonempty-object hypothesis); otherwise faithful to Loeffler 3.8.3 and true.**

### `gammaHNaive_representable_of_rigid` (T-H6) (GammaH.lean:150–153)
**Attacks:**
- **[FALSITY]** TRUE: immediate from `representable_iff` (T-E5) + T-H4, exactly as the docstring routes it.
- **[SRC]** Docstring promises Loeffler's "smooth and affine over Spec R" — the Lean statement asserts only `.Representable`. Same drift pattern as T-H4 (compare `gammaOneNaive_representable`, Representability.lean:134–138, which *does* carry the smooth∧affine clause). Fidelity fix: add the clause or a companion.
- **[HYP]** `hinv : IsUnit (N : R)` + `hrig` — no `Nontrivial R` needed here (conclusion, not an iff) ✓; hypotheses minimal given the route.
**Verdict:** **true but under-stated vs docstring** (smoothness/affineness dropped).

### `gammaFullNaive_not_rigid_of_le_two` (T-H7, DEF-1 fixed) (GammaH.lean:167–169)
**Attacks:**
- **[FALSITY]** TRUE as fixed. Witness chain: `hR` gives nonempty `S`; `hinv` makes `E[N]` étale so the full-level trivialisation `T → S` is finite étale **surjective** (fibres nonempty over geometric points), so `T ≠ ∅`; over `T`, tautological `L` with `[-1]•L = L` (`N ≤ 2 ⟹ 2P = 0 ⟹ -P = P`; `N = 1` degenerate case `L = (0,0)` also works); `e := ([-1], 𝟙)` is a genuine `EllObj`-iso (`isPullback` from iso-top over identity), `e ≠ Iso.refl` since `[-1] ≠ 𝟙` over nonempty base (points of odd order > 1 exist on geometric fibres); `pullSection` along it fixes `L`.
- **[HYP — DEF-1 audit]** Both added hypotheses are necessary: without `hinv`, over an `𝔽₂`-algebra `IsNaiveFullLevel 2` is empty (E[2] infinitesimal) so the problem is vacuously rigid — `hinv` correctly excludes it; without `hR`, `R = 0` (or `R` with only empty objects) is vacuously rigid — `hR` excludes it. Neither is stronger than needed (`N = 1`: `IsUnit (1 : R)` trivial ✓).
- **[TYPE]** `IsUnit ((N : ℕ) : R)` — the `(N : ℕ)` ascription is a no-op wart (N is already ℕ); `Nonempty X.base` uses the Scheme-to-type coercion ✓.
- **[SRC]** "`[-1]` acts trivially on `E[2]`" matches the docstring and the classical fact; design-D6 framing consistent with plan.md.
**Verdict:** **sound — DEF-1 fix adequate.**

### `gammaFullDrinfeldProblem` (GammaH.lean:183–189)
**Attacks:**
- **[DEP]** `map`'s membership sorry: base-change stability of Drinfeld full level. Mathematically TRUE (formation of `sectionsDivisor` commutes with base change — DS4a spec; `IsSubgroup` restricts along `T → S' → S`; `torsionIdeal` base-changes — T-B3a spec), **but** it again needs `pullSection` to commute with the ℤ-combinations building the divisor (`[aP + bQ]` ↦ `[a·pullP + b·pullQ]`) — the same hidden A6.δ/T-G2 dependency as `gammaHNaiveProblem`. Also the whole `obj` reads through `torsionIdeal`, which is **sorried data** (LevelStructure/Basic.lean:65 `:= sorry`) — DS-adjacent but note: `IsFullLevel` is currently a predicate on unconstructed data; every theorem about this problem is "modulo T-B3a's intended value".
- **[SRC]** KM 3.1 (Drinfeld Γ(N) definition) is PENDING-SOURCE(KM) per decomposition.md D8 — the *definition of record* of this functor has no verbatim quote yet. The prompt's "KM 1.5.1 quoted" claim: decomposition-km1.md covers divisor base change (KM 1.1.4, T-D12) with proofs, but a Ch.-3-level quote for Γ(N)-structure base change is **not** in hand. Gate stands.
- **[FALSITY]** The functor data is the right one (points of the correct set; contravariant via `pullSection`) — no truth defect at the definition level.
**Verdict:** **sound as a skeleton definition**, with (i) hidden rigidity dependency to surface, (ii) KM 3.1 quote-gate open, (iii) reliance on sorried `torsionIdeal` (registered).

### `gammaOneDrinfeldProblem` (GammaH.lean:193–197)
**Attacks:**
- **[DEP]** Membership sorry = base-change of `HasExactOrder`: true via DS4a base-change spec + `IsSubgroup` restriction; same hidden `pullSection`-additivity dependency (the `orderDivisor` is built from `((a+1) : ℤ)•P`).
- **[SRC]** KM 1.4.1 quote in hand ✓ (decomposition.md D2); the KM 3.2 locator ("[Γ₁(N)] := exact order N") pending — mild, content identical to 1.4.1.
- **[HYP]** No invertibility hypothesis — correct by design (Drinfeld register) ✓; KM Caution 1.4.3 (zero section has exact order pⁿ) is *embraced* by the definition — see T-H9 for where this bites.
**Verdict:** **sound** (same two caveats as its Γ(N) sibling).

### `gammaFullDrinfeld_representable` (T-H8) (GammaH.lean:204–206)
**Attacks:**
- **[FALSITY]** **FALSE as stated** (both conjuncts), for `N = 3` and any `R` with a char-3 point (e.g. `R = ℤ` or `𝔽₃`). Witness: `E` supersingular over `k̄ = F̄₃`; `[3]` is purely inseparable of degree 9, so `E[3] = Spec k[T]/(T⁹) = 9[0]` as closed subschemes; hence `(P,Q) = (0,0)` satisfies `IsFullLevel 3` (`Σ_{a,b}[a·0+b·0] = 9[0] = E[3]`; the full-set-of-sections/norm check: `Norm(f) = X₀⁹ = ∏ f(0)` — passes). `[-1]` is a non-refl automorphism over `𝟙`-base fixing `(0,0)` ⟹ `Rigid` fails; and `Representable ⟹ Rigid` (Yoneda + jointly-mono pullback legs forces `e.top = 𝟙`), so `Representable` fails too.
- **[SRC]** The project's **own quoted source contradicts the statement**: decomposition-gme2 §B9/Y.6 (GME, in hand): Aut-triviality "3|N or 4|N ⟹ … over ℤ[1/6]-schemes; **coprime m,n ≥ 3 ⟹ over ℤ**" — over ℤ needs two coprime divisors ≥ 3 (so `N = 3, 4, 5, 8, 9, p^k` are *not* covered over ℤ). The Lean statement's bare `3 ≤ N` over arbitrary `R` is a memory-formalisation of exactly the KM 4.7.2/5.1 material that is on the do-not-formalize-from-memory list; the ⧗KM gate correctly blocks proof but the *statement* is already wrong. Repair options: (a) add `hinv : IsUnit (N : R)` (matches plan.md's own headline "Y(N) for N ≥ 3 … over ℤ[1/N]"); or (b) keep arbitrary `R` with the GME hypothesis `∃ m n, m ∣ N ∧ n ∣ N ∧ 3 ≤ m ∧ 3 ≤ n ∧ Nat.Coprime m n` — and even then re-verify the representability half verbatim when KM lands.
- **[HYP]** No hypothesis mismatch can save it: the counterexample satisfies `NeZero`, `3 ≤ N` and lives over `R = ℤ`.
- **[DEP]** Downstream: Y-chain (Thm 2.6.8 plan) consumes this leaf — the chain's own steps (Y.6) carry the coprime-glueing structure, so fixing the statement aligns the leaf with its planned proof.
**Verdict:** **FALSE as stated — amend before any ticket is cut** (this is a statement-level defect the DEF-pass missed, not merely a gated proof).

### `gammaOneDrinfeld_representable` (T-H9) (GammaH.lean:210–212)
**Attacks:**
- **[FALSITY]** **FALSE as stated**, and refuted by a source **in hand**: KM Caution 1.4.3 ("over `𝔽_p` the zero section has exact order `pⁿ` for all `n`", quoted in decomposition.md D2). Take `N = 4`, `R = ℤ`, any `E/F̄₂` (even ordinary): `orderDivisor 0 4 = 4[0] = ker F²` (local equation `T⁴`; Frobenius kernels are subgroups), so the zero section `∈ obj` with `IsGammaOne 4`; `[-1] ≠ 𝟙` fixes it ⟹ not rigid ⟹ not representable. Same for every prime power `N = p^k ≥ 4` in char `p`, and even for `N = 12` in char 2 (structure degenerates to an order-3 point fixed by a unipotent in `Aut(E_ss/F̄₂) ≅ SL₂(𝔽₃)`).
- **[SRC]** "KM 5.x" quote missing (⧗KM ✓), and the classical `N ≥ 4` theorem lives over `ℤ[1/N]` (plan.md's own headline line agrees: "`Y₁(N)` for `N ≥ 4` … over `ℤ[1/N]`"). The over-ℤ generalisation needs whatever fine print KM actually has — statement must not assert it before the quote exists.
- **[HYP]** Repair: add `IsUnit (N : R)`, or the appropriate KM-verbatim condition when the text lands.
**Verdict:** **FALSE as stated — amend** (KM 1.4.3, already quoted in the project, is the refuting instance; the leaf and the caution quote cannot both stand).

### `LevelledHom` (GammaH.lean:224–228)
**Attacks:**
- **[FALSITY/role]** Same endo defect as `HomOver`: `⟨[1+N]-as-HomOver, hP, hQ⟩` is a non-invertible `LevelledHom X X` (level fixed since `N•P = 0`). So the "levelled groupoid" is not a groupoid, and the docstring's "for `N ≥ 3` this groupoid is discrete on isomorphism classes (`aut_trivial_of_fullLevel`)" inherits T-G3's falsity (Hom-sets are not `{𝟙}`; only Aut is trivial).
- **[TYPE]** Fields typecheck: `X.2.1.1.1 : S ⟶ X.1.E`, `hom.hom : X.1.E ⟶ Y.1.E`, target `Y.2.1.1.1` ✓ (the projection chains through `FullLevelPt`'s subtype/product are correct). **No `@[ext]`** — the category-law sorries below want it (provable manually, but add the attribute).
- **[DEP]** `Stack.lean`'s `hdesc`/conclusion use `≅` in this category — isos are honest levelled isos, so the Stack statement is unaffected by the endo defect ✓ (checked).
**Verdict:** **definition usable; role/docstring defective; add `@[ext]`** and either an `IsIso hom` variant or systematic ≅-usage downstream.

### `fullLevelGroupoid` (instance) (GammaH.lean:230–237)
**Attacks:**
- **[DEP]** All five sorries (`id`/`comp` level-Props, three laws) are TRUE and easy: `id` levels by `comp_id` in `Scheme`; `comp` levels by chaining `level_w₁/₂`; laws reduce to the base category after an ext-principle for `LevelledHom` (missing `@[ext]` is the only friction).
- **[FALSITY]** As a `Category` instance: sound. As "the levelled *groupoid*": misnomer (see `LevelledHom`); no `Groupoid` instance is (or can be) given.
- **[TYPE]** `Category (Σ E, E.FullLevelPt N)` over `Type (u+1)` objects with `Type u` homs ✓; `noncomputable instance` is an odd combination for pure data + Props (comp data is computable; the marker is harmless but gratuitous).
**Verdict:** **sound instance, easy sorries; rename/reframe the groupoid claim.**

---

## Coarse.lean

### `HomOver.mapPoint` (Coarse.lean:37–39)
**Attacks:**
- **[FALSITY]** Correct transport: `⟨P.1 ≫ f.hom, …⟩` with the right `over_w` rewrite ✓.
- **[DEP]** No additivity spec (`mapPoint (P + Q) = mapPoint P + mapPoint Q`) — true by rigidity, needed the moment anyone reasons about `GammaHClasses`; same hidden-dependency family as `pullSection`.
- **[HYP]** Defined for arbitrary `HomOver` — inherits the non-iso breadth; harmless for the definition itself, load-bearing for `GammaHClasses` (below).
**Verdict:** **sound** (spec gap noted).

### `GammaHClasses` (Coarse.lean:54–60)
**Attacks:**
- **[FALSITY]** **Defective relation.** `f` ranges over all `HomOver`s, which include non-isomorphisms. Concretely (`N = 2`, any `H`, `S = Spec ℚ̄`): a 3-isogeny `f : E → E'` restricts to an isomorphism `E[2] ≅ E'[2]`, so `(E,(P,Q)) ∼ (E',(fP,fQ))` with `j(E) ≠ j(E')` — the quotient collapses odd-degree-isogenous curves, not just isomorphic ones. For `N = 1` it is worse: the zero `HomOver` relates everything (level `(0,0)` forced), so `GammaHClasses S 1 H` is a **singleton**. This is not the point-set of any coarse `Y_{P_H}`.
- **[SRC]** The docstring justifies equivalence-ness by "since the morphisms are isomorphisms, T-G1" — T-G1 is false (Groupoid.lean audit), so the justification is void and the defect is live. Loeffler §3.8 Remark (1)'s `P̃_H` classes are iso-classes; fix: require `IsIso f.hom` (or use `a.1 ≅ b.1` + level clauses, or reuse the `fullLevelGroupoid` ≅ plus `glSmul`).
- **[FALSITY — seed's orientation question, adjudicated]** g-then-f vs f-then-g: with the (rigidity-provided) additivity of `mapPoint`, the two compositions generate the same equivalence closure, and `Quot` takes the generated equivalence anyway — orientation is benign ✓; raw-relation transitivity/symmetry failure is absorbed by `Quot` ✓. The defect is solely the non-iso `f`.
- **[TYPE]** `Quot` (not `Quotient`+`Setoid`) is the right tool for a non-equivalence generator ✓; `Type (u+1)` ✓.
**Verdict:** **DEFECTIVE — add invertibility of `f`.** (After the fix, the definition matches "join of H-action and pointed isomorphism".)

### `jLine_coarse_points` (T-M1) (Coarse.lean:67–68)
**Attacks:**
- **[FALSITY/junk]** As a standalone, `Nonempty (IsoClasses ≃ k)` is a pure **cardinality** statement (both sides have cardinality `#k` for every algebraically closed `k`), so it is true for trivial reasons and pins nothing. It is rescued only because T-M1a (below) supersedes it with the j-pin; keep them adjacent or merge.
- **[SRC]** Silverman III.1.4(b) + "KM 8.2 ⧗" — KM Ch. 8 quote pending (recorded in file ✓); Silverman covers the honest content fibrewise ✓.
- **[TYPE]** `Equiv` between `Type (u+1)` (`IsoClasses`) and `Type u` (`k`) is legal ✓; `Spec (.of k)` ✓.
**Verdict:** **true but content-light alone; acceptable as a stepping-stone given T-M1a.**

### `jLine_coarse_points_j` (T-M1a) (Coarse.lean:73–77)
**Attacks:**
- **[FALSITY — determinacy of the clause]** If one `E` matches models of `W` and `W'`, then `W ≅ W'` over `k̄` hence `j` equal — the clause is consistent. Subtlety: `e : E.E ≅ projModel W` is **not required to be pointed** (only `e.hom ≫ projModelπ W = E.π`); over an algebraically closed field this is benign (translations make any curve-iso pointed without changing `j`), so determinacy survives — but over general bases it would not; fine here, worth a comment.
- **[DEP]** `projModel/projModelπ` are DS1 **sorried data** (WeierstrassModel.lean:74–80): the statement quantifies over unconstructed data; meaningful only through T-A2's `IsWeierstrassModel` spec — registered ✓ (per prompt, acknowledged). Nonvacuity of the ∀-clause (every class contains such a `(W, e)`) is the locally-Weierstrass theorem over a field — a genuine proof obligation, satisfied classically ✓, so β is pinned on *all* classes ✓.
- **[TYPE]** `(_ : W.IsElliptic)` as a plain binder: Lean 4 registers local hypotheses of class type as local instances, so `W.j` elaborates ✓ (compile-time check — note the recorded green build predates the DEF-fix edits; re-verify on next build).
- **[SRC]** Silverman III.1.4(b) exactly ✓; j-invariance under iso is the honest content.
**Verdict:** **sound — this is the statement that gives T-M1 content.**

### `exists_coarse_gammaH` (T-M2) (Coarse.lean:85–91)
**Attacks:**
- **[FALSITY/junk]** **Vacuous as stated.** The conclusion demands only `Nonempty (classes ≃ fibre)` for an *unconstrained* `∃ Y σ` — a cardinality condition. `Y := 𝔸¹_{Spec R}` satisfies it outright: for every algebraically closed `k`, both sides have cardinality `#k` (iso-classes-with-level over `k̄` ≈ `#k`; the defective collapse only merges countable isogeny orbits, leaving `#k`; fibres of `𝔸¹` = `k`). So the theorem as written asserts nothing about moduli. Loeffler's quoted Remark (1) has the pin the Lean statement dropped: the **map** `P̃_H(S) → Y_{P_H}(S)` (natural, defined for all `S`, bijective for alg. closed `S`). Minimum repair: fix `Y` with a family of maps `classes → fibre` given by an actual construction (or at least j-compatibility/naturality clauses, as T-M1a does for level 1).
- **[FALSITY upstream]** Even with a pin, the LHS is currently the defective `GammaHClasses` (isogeny collapse) — two independent repairs required.
- **[HYP]** `hinv : IsUnit (N : R)` sensible (matches `ℤ[1/N]` in the source); no `Nontrivial R` needed for an existential ✓.
- **[SRC]** Loeffler §3.8 Remark (1) quote present in the docstring ✓ — quote-statement mismatch (map dropped) rather than quote-missing; "KM Ch. 8 ⧗" pending as recorded.
**Verdict:** **DEFECTIVE (junk-statement class — the decomposition's own kill-category); restate with the transported map before ticketing.**

---

## Stack.lean

### `levelledCurve_descent_of_torsor` (T-E10 v2, DEF-2) (Stack.lean:68–83)
**Attacks:**
- **[FALSITY]** Statement is TRUE in this form (rigidified torsor descent): mere `hdesc`-isos + Aut-triviality (from `3 ≤ N`, `N` invertible, full level) force the cocycle (GME p. 148, quoted in the docstring ✓), and the ample `[0]`-divisor descends the projective family. The DEF-2 replacement correctly removed the false cocycle-free fppf form (sextic-twist obstruction acknowledged in the docstring ✓).
- **[SRC — seed's θ(g) direction question, adjudicated]** GME's `θ(g) : g^*(𝐄, φ_N) ≅ (𝐄, φ_N)` (decomposition-gme2 Y.5) has the **same** `φ_N` on both sides — the G-twist acts through the base, not through the `GL₂`-matrix action. `hdesc`'s `⟨E'.baseChange (σ g), pullAlong (σ g) L'⟩ ≅ ⟨E', L'⟩` matches exactly ✓ (no `φ∘g` should appear; the seed's worry is resolved in the file's favour).
- **[TYPE — torsor map]** `Sigma.desc (fun g => pullback.lift ((σ g).hom.left) (𝟙 T') _)`: component over `g` is `t ↦ (g·t, t)` — matches GME's `G × T ≅ T ×_S T` ✓; the `lift` side-condition proof term is the right `Over.w` ✓. Wart: `G : Type` (universe 0) — works for finite coproducts in `Scheme.{u}` but is a needless universe restriction; prefer `G : Type u` or polymorphism.
- **[HYP]** `hinv : IsUnit (N : Γ(T', ⊤))` is stated over `T'`, GME's is over the base: equivalent here — `f` surjective makes N-invertibility on `T'` and on `T` coincide (unit ⟺ unit in every residue field, and every point of `T` lifts) ✓; harmless, though `NIsInvertible T' N` would be the house form. `[Flat f][LocallyOfFinitePresentation f][Surjective f]` are implied by `htorsor` + `G` finite in the classical setting but harmless as explicit hypotheses ✓. Degenerate checks: `G` trivial ⟹ `f` iso ⟹ trivially true; `T' = ∅` ⟹ `T = ∅` ⟹ need the empty elliptic curve to exist (it does) ✓.
- **[DEP]** The proof route requires the **iso-form** of T-G3 (Aut-triviality) — currently false-as-stated in Groupoid.lean; the repair there is a prerequisite for this leaf's discharge. Also needs `pullAlong` functoriality specs (unstated, see above) and the AINTLIB Galois-descent engines (stream DESC) as recorded.
**Verdict:** **sound (DEF-2 fix is correct and well-oriented)**; blockers: T-G3 repair, `pullAlong` specs, universe wart.

### `moduliProblem_fppf_separated` (T-E11) (Stack.lean:90–96)
**Attacks:**
- **[FALSITY — seed's epi question, adjudicated]** TRUE. Via `hP`, both values transport to `{h : T ⟶ Z // h ≫ f₀ = g}`; the **naturality clause inside `RelativelyRepresentable`** (EllCategory.lean:118–121) is exactly the square needed to transfer (the seed's "composition attack" is defused — but note the transfer *does* consume that clause; a `RelativelyRepresentable` without it would make this statement unprovable). Injectivity then reduces to: fppf covers are **epimorphisms of schemes** (`f ≫ h₁ = f ≫ h₂ ⟹ h₁ = h₂`) — true by fppf/fpqc descent of morphisms (representables are fppf sheaves; SGA 1 VIII).
- **[DEP]** That epi-ness is a genuine mathlib-gap check: descent-data infrastructure is merged but "fppf cover ⟹ epi (subcanonicity)" must be located or proved — small but not free; belongs on the DESC stream ticket, currently unlisted.
- **[SRC]** Cited "KM 4.1–4.2" is **not in hand** (Ch. 4 on the pending list) and "Loeffler Prop 3.8.2" does not state fppf-separatedness — this statement currently has **no verbatim source**; per the project's own gate it should be marked PENDING-SOURCE (it is a formal lemma, but the gate is the gate).
- **[HYP]** Stated only for relatively representable `P` — right scope (the four basic problems); `Flat/LocallyOfFinitePresentation/Surjective` as explicit Prop-arrows ✓. Degenerate `T' = ∅`: then `Surjective f` forces `T = ∅` and injectivity is into a subsingleton — holds ✓.
- **[TYPE]** `(X.pullbackAlongMap g f).op : op (pullbackAlong g) ⟶ op (pullbackAlong (f ≫ g))` — direction and `P.map` application typecheck ✓.
**Verdict:** **sound**; add the fppf-epi discharge item and a source marker. **Stale docstring bug (file-level):** Stack.lean:18–24 still advertises `ellipticCurve_fppf_descent` as item 1 — that declaration no longer exists post-DEF-2 (plan.md's DESC row has the same stale pointer).

---

## Summary table

| # | Declaration (file:line) | Verdict | Action |
|---|---|---|---|
| 1 | `HomOver` (Groupoid:34) | role-defective (not iso-closed) | add iso variant / fix role |
| 2 | `Category (EllipticCurve S)` (Groupoid:43) | sound (laws proved, not sorried) | fix docstring "groupoid" |
| 3 | `isIso_homOver` T-G1 (Groupoid:55) | **FALSE** (`[2]`) | delete/restate with cartesian Hom |
| 4 | `IsoClasses` (Groupoid:61) | sound | — |
| 5 | `aut_trivial_of_fullLevel` T-G3 (Groupoid:71) | **FALSE** (`[1+N]`) | endo → iso; then matches GME p.151 |
| 6 | `FullLevelPt` (GammaH:54) | sound | naming note |
| 7 | `glSmul` (GammaH:64) | sound (indices = φ∘g, verified) | — |
| 8 | `glSmul_mul` T-H2a (GammaH:74) | **FALSE** (left law for right action) | `glSmul (g*h) L = glSmul h (glSmul g L)` |
| 9 | `hOrbitSetoid` (GammaH:79) | sound | discharge via corrected T-H2a |
| 10 | `FullLevelPt.pullAlong` (GammaH:86) | sound | add functoriality specs |
| 11 | `gammaHNaiveProblem` (GammaH:107) | sound mod **hidden dep** | surface `pullSection_add` (A6.δ/T-G2 edge) |
| 12 | `gammaHNaive_bot` T-H1 (GammaH:119) | true | N=1 val-edge note |
| 13 | `gammaHNaive_relativelyRepresentable` T-H4 (GammaH:127) | true, under-stated | add finite-étale conjunct |
| 14 | `gammaHNaive_rigid_iff` T-H5 (GammaH:136) | fails at `R = 0` | add `Nontrivial R`; else faithful |
| 15 | `gammaHNaive_representable_of_rigid` T-H6 (GammaH:150) | true, under-stated | add smooth∧affine per docstring |
| 16 | `gammaFullNaive_not_rigid_of_le_two` T-H7 (GammaH:167) | sound (**DEF-1 adequate**) | — |
| 17 | `gammaFullDrinfeldProblem` (GammaH:183) | sound skeleton | KM 3.1 quote-gate; hidden dep; torsionIdeal DS |
| 18 | `gammaOneDrinfeldProblem` (GammaH:193) | sound skeleton | same |
| 19 | `gammaFullDrinfeld_representable` T-H8 (GammaH:204) | **FALSE** (ss char 3, (0,0)) | add coprime-`m,n ≥ 3` hyp (GME) or `IsUnit (N : R)` |
| 20 | `gammaOneDrinfeld_representable` T-H9 (GammaH:210) | **FALSE** (KM 1.4.3 zero-section, char 2, N=4) | same repair |
| 21 | `LevelledHom` (GammaH:224) | usable; role-defective | `@[ext]`; iso framing |
| 22 | `fullLevelGroupoid` (GammaH:230) | sound instance; misnomer | easy sorries; rename claim |
| 23 | `HomOver.mapPoint` (Coarse:37) | sound | additivity spec gap |
| 24 | `GammaHClasses` (Coarse:54) | **DEFECTIVE** (isogeny collapse) | require `IsIso f.hom` |
| 25 | `jLine_coarse_points` T-M1 (Coarse:67) | true, cardinality-only | keep with T-M1a |
| 26 | `jLine_coarse_points_j` T-M1a (Coarse:73) | sound | unpointed-`e` comment |
| 27 | `exists_coarse_gammaH` T-M2 (Coarse:85) | **DEFECTIVE/vacuous** (𝔸¹ satisfies it) | restate with Loeffler's map |
| 28 | `levelledCurve_descent_of_torsor` T-E10v2 (Stack:68) | sound (**DEF-2 adequate**) | needs fixed T-G3; `G : Type u` |
| 29 | `moduliProblem_fppf_separated` T-E11 (Stack:90) | sound | fppf-epi discharge item; source marker; stale docstring |

## QUOTE-MISSING list (per the project's do-not-formalize-from-memory gate)

1. **T-G1 `isIso_homOver`** — "KM 2.4-adjacent ⧗KM": no quote, and no quote can exist for the iso claim (the statement is false; KM 2.4 is about hom-ness).
2. **T-H8 `gammaFullDrinfeld_representable`** — KM 4.7.2/5.1: no verbatim quote; the in-hand GME quote (coprime `m,n ≥ 3` for over-ℤ Aut-triviality, decomposition-gme2 §B9/Y.6) *contradicts* the current form.
3. **T-H9 `gammaOneDrinfeld_representable`** — KM 5.x: no quote; refuted by the in-hand KM Caution 1.4.3 quote.
4. **`gammaFullDrinfeldProblem`** — KM 3.1 (Drinfeld Γ(N) definition): PENDING-SOURCE(KM) (decomposition.md D8); base-change-of-Γ(N)-structures (Ch.-3 level) also unquoted (decomposition-km1 covers only Ch.-1 divisor base change).
5. **`gammaOneDrinfeldProblem`** — KM 3.2 locator pending (KM 1.4.1 quote in hand covers the content).
6. **`moduliProblem_fppf_separated`** — KM 4.1–4.2 not in hand; the Loeffler 3.8.2 citation does not cover fppf-separatedness. No verbatim source for this statement.
7. **`jLine_coarse_points`/`_j`** — KM 8.2 ⧗ pending (Silverman III.1.4(b) suffices for content; KM reconciliation open).
8. **`exists_coarse_gammaH`** — Loeffler §3.8 Remark (1) quote present but the Lean statement drops the quoted map `P̃_H(S) → Y_{P_H}(S)` (quote–statement mismatch); KM Ch. 8 ⧗ pending.
9. **`gammaHNaiveProblem` (general-H quotient presentation)** — KM Ch. 3 + 7 locators pending (Loeffler 3.8.1 quote present, so statement-sourced).
10. **Stale cross-references**: Stack.lean:18–24 and plan.md DESC row still cite the deleted `ellipticCurve_fppf_descent`.

**Cross-cutting recommendation.** One root cause generates findings 1, 3, 5, 21, 22, 24: pointed-morphism structures (`HomOver`, `LevelledHom`) are used where the moduli groupoid's *isomorphisms* are meant. Fix once (add `isPullback`/`IsIso` or an ≅-wrapper) and re-derive. Second root cause (11, 17, 18, 23): `EllHom` carries no group-compatibility, so every `pullSection`/`mapPoint` additivity silently consumes group-law uniqueness (A6.δ) — state it as a spec lemma and restore the dependency edge that the "nothing depends on the canonicity project" amendment removed.