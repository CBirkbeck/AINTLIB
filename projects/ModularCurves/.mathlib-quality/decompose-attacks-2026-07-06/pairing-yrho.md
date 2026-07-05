<!-- Adversarial /develop --decompose attack log, agent ab644fca25c1b47b0, archived 2026-07-06 -->

All symbols are grounded. I have everything needed. Here is the adversarial verification report.

---

# ADVERSARIAL VERIFICATION — WeilPairing/Basic.lean + ModularCurve/YRho.lean

**Method.** Both files read in full. Context cross-checked against `plan.md` (DS register), `decomposition.md` (§F Buzzard, source-gate), `decomposition-gme2.md` (§C = GME 2.6.4 pairing chain), and `expert-review/2026-07-05/reply.md` (Q4/Q6). Mathlib ground-truth read from source in `.lake/packages/mathlib`: `modularCyclotomicCharacter` (+`spec`/docstring/`hn` shape), `Field.absoluteGaloisGroup`, `krullTopology` (instance on `L ≃ₐ[K] L`), `Matrix.GeneralLinearGroup.det : GL n R →* Rˣ`, `IsAffineHom`, `IrreducibleSpace`. Project symbols grounded: `EllipticCurve extends EllipticCurveGeom` with total-space field `E : Scheme`; `Point g := {h : T ⟶ E.E // h ≫ E.π = g}`; `mulByHom (n:ℤ) := (mulBy n).left`; `pointAddCommGroup`, `Point.restrict`, `zeroPoint`, `torsionπ`, `pointToTorsion(_torsionπ)`, `muNPointsEquiv`, `baseChange`. Attack tags: **[T]** type/elaboration · **[C]** convention/orientation · **[H]** hypothesis-strength · **[S]** source-faithfulness · **[M]** math-correctness. No build run; no edits.

**Headline: 2 REAL defects + 1 hypothesis gap.** `yRho_representable` REJECTED (quotient relation far too coarse), `yRho_geometricallyIrreducible` NEEDS-FIX (false as universally stated), `coord` NEEDS-FIX (missing `over_T`). The convention spine (`symplectic` / `det_cyclo` / `p_equivariant`) is **mutually consistent and matches the Silverman pin** — survives hard attack.

---

## WeilPairing/Basic.lean

### `weilPairing` (Basic.lean:42, DS4 data-sorry)
- **[T]** Type `pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N` elaborates: `torsionπ N : E.torsion N ⟶ S`, self-pullback is `E[N] ×_S E[N]`, `muN S N` real. `[NeZero N]` present. OK.
- **[S]** Construction of record = GME 2.6.4 §C.2 (`decomposition-gme2.md`: "key-lemma ⟹ morphism Ker(π) × Ker(^tπ) → μ_N"); `^t[N]=[N]` by B8 makes it `E[N]×E[N]`. Cited source present.
- **[M]** Registered data — sorriness intentional (DS4). No property assumed except via specs. Consistent with "consume only through `weilPairing` + specs" (module docstring).
- **Verdict: SURVIVED** (data-sorry, correctly registered).

### `weilPairing_over` (Basic.lean:46)
- **[T]** `E.weilPairing N ≫ muNπ S N = pullback.fst _ _ ≫ E.torsionπ N` — both `E[N]×_S E[N] ⟶ S`; `muNπ = pullback.fst` structure map. Typechecks.
- **[C]** Direction: says the pairing lands over `S` via the FIRST factor's structure map. Since `torsionπ∘fst = torsionπ∘snd` on the pullback, either factor pins the same base map — no orientation ambiguity.
- **[H]** Minimal (single equation); it is the "morphism over S" spec DS4 requires. Not over-determined.
- **Verdict: SURVIVED.**

### `weilPairingEval` (Basic.lean:53, real def)
- **[T]** `muNPointsEquiv S N g ⟨pullback.lift (pointToTorsion x hx) (pointToTorsion y hy) (by simp) ≫ weilPairing N, …⟩` — the proof uses `weilPairing_over` + `pullback.lift_fst` + `pointToTorsion_torsionπ`; lands in `{a : Γ(T,⊤) // a^N = 1}`. Coherent.
- **[H]** Requires `hx, hy` (raw kill) to build `pointToTorsion`; both consumed. Correct.
- **[M]** "Real construction modulo registered data" — honest; the `by simp` obligation is the two factors agreeing on base. OK.
- **Verdict: SURVIVED.**

### `weilPairingEval_add_left` (Basic.lean:67, T-C2)
- **[C]** Left-additive → target-multiplicative: `e(x+x',y)=e(x,y)·e(x',y)`. Standard bilinearity orientation. ✓
- **[H]** Four kill-hyps `hx,hx',hy,hxx'`; `hxx'` for `x+x'` is derivable from `hx,hx'`+group law but is **needed to form** `weilPairingEval (x+x') y hxx' hy` (it is an explicit argument). Benign, not removable without inlining.
- **[S]** Cites "KM 2.8.2; Silverman III.8.1(a)". KM 2.8 is under the project's own **do-not-formalize-from-memory** gate; no verbatim quote in provided context → see QUOTE-MISSING. Statement itself is the standard bilinearity axiom, correct.
- **[M]** With `_self` (below), {add_left, self} generates full bilinearity + antisymmetry — an adequate generating spec; no right-additivity gap.
- **Verdict: SURVIVED** (source-quote pending — QUOTE-MISSING on KM 2.8/Silverman citation).

### `weilPairingEval_self` (Basic.lean:76, T-C2′ alternating)
- **[C]** `e(x,x)=1` — alternating (Silverman III.8.1(b)). Correct; note this is the *alternating* form (stronger than antisymmetric), the right choice matching Buzzard's "alternating … pairing".
- **[H]** Single point `x`, single kill-hyp — minimal.
- **[S]** KM 2.8 / Silverman III.8.1(b) — same gate as above; no verbatim quote → QUOTE-MISSING.
- **Verdict: SURVIVED** (QUOTE-MISSING on citation).

### `weilPairingEval_nondegenerate` (Basic.lean:86, T-C3)
- **[M]** Quantifier `(∀ y with hy, e(x,y)=1) → x = zeroPoint t`. Matches **GME §C.4 verbatim** (`decomposition-gme2.md`: "⟨P,Q⟩ = 1 ∀Q ⟹ … P = 0"). Over `k` alg. closed, `E.Point t` ranges over all geometric `N`-torsion, so the hypothesis is the genuine fibrewise nondegeneracy. ✓
- **[T]** `[IsAlgClosed k]`, `t : Spec (.of k) ⟶ S`, values in `Γ(Spec (.of k),⊤)`. `x = E.zeroPoint t` well-typed. OK.
- **[H]** `x` only raw-killed (hx) — correct and sufficient (seed's "fine"). Fibrewise surrogate for full perfectness (AG-CD) is explicitly flagged in docstring.
- **Verdict: SURVIVED** (GME C.4 quote present).

### `weilPairingEval_restrict` (Basic.lean:97, T-C2a base-change)
- **[C/T]** Γ-map direction: `k : T' ⟶ T` ⟹ `k.op : op T ⟶ op T'` ⟹ `Scheme.Γ.map k.op : Γ(T) ⟶ Γ(T')`. Applied to `e(x,y)∈Γ(T)` gives `Γ(T')`; LHS `e(x|_{T'},y|_{T'})∈Γ(T')`. **Directions match.** ✓
- **[T]** `.hom` extracts the `CommRingCat` ring hom; subtype-coe consistent on both sides (`{a//a^N=1} ↪ Γ`); ring hom preserves `^N=1`, so RHS is a root of unity too. OK.
- **[S]** Pins base-change naturality — **expert review Q4 verbatim** ("compatible with arbitrary base change"; "over nonreduced bases, equality of morphisms is not generally detected on geometric fibres"). Faithful.
- **Verdict: SURVIVED.**

### `weilPairingEval_mul` (Basic.lean:110, T-C2b divisibility)
- **[C/M] EXPONENT RECOMPUTED INDEPENDENTLY.** Lattice model `E ≅ ℂ/(ℤ+ℤτ)`: `N`-torsion `x=(a₁+a₂τ)/N`, `e_N(x,y)=exp(2πi(a₁b₂−a₂b₁)/N)`. As `NM`-torsion, `x=(Ma₁+Ma₂τ)/(NM)`, coords `(Ma₁,Ma₂)`, so `e_{NM}(x,y)=exp(2πi·M²(a₁b₂−a₂b₁)/(NM))=exp(2πi·M(a₁b₂−a₂b₁)/N)=e_N(x,y)^M`. **Exponent `M` CONFIRMED.** ✓
- **[T]** `haveI : NeZero (N*M) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩` correctly discharges the instance for `weilPairingEval (N := N*M)`; `haveI …; term` scopes it to the LHS; both sides `Γ(T,⊤)`. Plumbing correct.
- **[H]** Takes both `hx,hy` (kill by N) and `hx',hy'` (kill by N·M). `hx',hy'` derivable from `hx,hy` (N∣NM) but needed as explicit args to `weilPairingEval (N:=N*M)`. Benign.
- **[S]** Cites "Silverman III.8.4-type; ⧗KM 2.8". No verbatim quote in provided context (KM 2.8 gated; gme2 §C gives no explicit `e_{NM}=e_N^M`). Math verified by my recomputation → QUOTE-MISSING on the citation only.
- **Verdict: SURVIVED** (exponent independently confirmed; QUOTE-MISSING on source).

### `weilPairingEval_symplectic` (Basic.lean:124, T-C2c — the pin)
- **[C] ORIENTATION — the load-bearing pin.** Exponent `(a*d − b*c)` = **`ad − bc`** (the determinant), NOT `bc − ad`. Matches **reply.md §Q6 verbatim**: "`e_N(aP + bQ, cP + dQ) = e_N(P,Q)^{ad−bc}`". ✓ Silverman convention pinned correctly.
- **[C] `Int.emod` sign.** `((ad−bc) % (N:ℤ)).toNat`: for `N>0` (from `[NeZero N]`), `Int.emod` is nonneg and `< N` (`Int.emod_nonneg`/`emod_lt_of_pos`), so `.toNat` is faithful (no clamping). Reducing mod N is harmless (`e_N(P,Q)` has order ∣ N). ✓
- **[H]** `h₁,h₂` (kill of `a•P+b•Q`, `c•P+d•Q`) derivable from `hP,hQ`+group laws, but **required to form** the `weilPairingEval` calls — benign-but-noted (seed's read confirmed). `a•P` is the `ℤ`-zsmul from `pointAddCommGroup`. Types OK.
- **Verdict: SURVIVED** (orientation `ad−bc` matches the Q6 pin verbatim).

---

## ModularCurve/YRho.lean

### `GalQ` (YRho.lean:46, abbrev)
- **[T] Instance-availability (the real question).** `abbrev GalQ := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ` is the *unfolded* form; `Field.absoluteGaloisGroup`'s `deriving Group/TopologicalSpace/IsTopologicalGroup` attaches to the head symbol `absoluteGaloisGroup`, NOT to the unfolded `AlgEquiv`. **However** the needed instances resolve via *general* mathlib instances on `L ≃ₐ[K] L`: `AlgEquiv.aut` (Group) and **`instance krullTopology (K L) […] : TopologicalSpace (L ≃ₐ[K] L)`** (verified line 137 of KrullTopology.lean). So `[Group GalQ]` and `[TopologicalSpace GalQ]` both resolve. ✓
- **[S]** Docstring says instances apply "because" it's the unfolded form — slightly misattributes the mechanism (they apply via general instances, not via `absoluteGaloisGroup`'s deriving) but the *conclusion* holds. Doc-nit only.
- **[T]** `σ.toRingEquiv` (`AlgEquiv.toRingEquiv`) and `σ (elt)` (FunLike on `AlgEquiv`) both available. ✓
- **Verdict: SURVIVED** (defeq to `Field.absoluteGaloisGroup ℚ`; instances resolve via `krullTopology`/`AlgEquiv.aut`; minor doc imprecision).

### `card_rootsOfUnity_algClosureQ` (YRho.lean:50, T-F0)
- **[T] Shape match vs `hn`.** mathlib `modularCyclotomicCharacter {n}[NeZero n] (hn : Fintype.card {x // x ∈ rootsOfUnity n L} = n)`. This theorem's type is `Fintype.card { x // x ∈ rootsOfUnity N (AlgebraicClosure ℚ) } = N` — **token-identical** to `hn` with `n:=N`, `L:=AlgebraicClosure ℚ`. Directly usable as the `hn` argument (as it is in `det_cyclo`/`p_equivariant`). ✓
- **[T] Fintype instance.** The subtype's `Fintype` resolves the same way mathlib's own `hn`-type does (domain + `NeZero N`); even if two Fintype instances existed, `Fintype.card` is invariant and `hn` is a hypothesis so any proof of the exact prop suffices. No mismatch.
- **[M]** `|μ_N(ℚ̄)| = N` for char-0 alg-closed — true. Standard mathlib discharge.
- **Verdict: SURVIVED** (shape equals `modularCyclotomicCharacter`'s expected argument).

### `GaloisRepData` (YRho.lean:58, structure) — incl. `ρ, ker_open, det_cyclo, p, p_equivariant`
- **[T] `ker_open`.** `IsOpen (X := GalQ) (MonoidHom.ker ρ : Set GalQ)` — needs `TopologicalSpace GalQ` (✓ via `krullTopology`) and `MonoidHom.ker ρ : Subgroup GalQ` coerced to `Set`. Typechecks. Correct rendering of "continuous ⟺ open kernel" for a hom to a discrete finite group.
- **[C] `det_cyclo` — inverse-ambiguity adjudication (seed).** `Matrix.GeneralLinearGroup.det (ρ σ) = modularCyclotomicCharacter ℚ̄ (…) σ.toRingEquiv`, both `(ZMod N)ˣ`. mathlib's `modularCyclotomicCharacter` is characterised (docstring L207-211; `spec` L222) by **`g(ζ)=ζ^{χ(g)}`** — exactly the reviewer's χ. reply.md Q6: "with σ(ζ)=ζ^{χ(σ)} the determinant … is χ". So `det ρ = χ` (NOT χ⁻¹). **No inverse ambiguity**: the transformation `e(gv,gw)=e(v,w)^{det g}` plus equivariance `e(σP,σQ)=σ(e(P,Q))=e(P,Q)^{χ(σ)}` force `det ρ = χ` independent of left/right GL₂-action convention. ✓
- **[C] `p_equivariant` consistency (seed).** `σ(p x)=p(x^{(χ σ).val})`. Since `p` is `MulEquiv` and mathlib `spec` gives `σ(p x)=(p x)^{(χ σ).val}=p(x^{(χ σ).val})`, this is **forced and uses the same χ as `det_cyclo`** — both sides of the convention agree. Exponent `((χ σ : (ZMod N)ˣ) : ZMod N).val : ℕ` is **exactly mathlib's `spec` form** (`t ^ ((χ … g) : ZMod n).val`); nat-power `x^val` equals the ZMod-action transport because `val ≡ χσ (mod N)` and `Multiplicative (ZMod N)` is N-torsion. ✓
- **[S]** "alternating Gal-equivariant perfect pairing to μ_N(ℚ̄)" — Buzzard p.33 verbatim (decomposition.md F2). The `p : Multiplicative (ZMod N) ≃* rootsOfUnity N ℚ̄` renders "Λ²ρ ≅ μ_N unique up to (ℤ/N)ˣ". Faithful.
- **Verdict: SURVIVED** — `det_cyclo` and `p_equivariant` use the **same χ** (mathlib's `modularCyclotomicCharacter`), mutually consistent, matching the Silverman pin; no hidden inverse.

### `vRho` / `vRhoπ` (YRho.lean:81, 84, DS5 data-sorries)
- **[T]** `vRho D : Scheme.{0}`, `vRhoπ D : vRho D ⟶ Spec (.of ℚ)`. Universe 0 (ℚ-schemes). OK.
- **[S]** Grothendieck–Galois descent of constant `(ℤ/N)²`; Loeffler §3.6 "scary lemma" quote present (decomposition.md F1). Registered DS5.
- **[H]** Pinned by finite-étale/Galois equivalence (reply.md Q4 verbatim: "the pinning spec should be the finite-étale/Galois equivalence, not merely a description of geometric points") — the register (DS5) records this correctly; the *equivalence* spec is T-F1's gate.
- **Verdict: SURVIVED** (data-sorry, correctly registered).

### `vRhoπ_finite_etale` (YRho.lean:88, T-F1a)
- **[T]** `IsFinite (vRhoπ D) ∧ Etale (vRhoπ D)`. Both morphism classes exist. OK.
- **[M]** Degree N² claimed in docstring; the conjunction states finite + étale (the numeric degree is prose, not in the Prop — acceptable, degree is recoverable).
- **[S]** Matches "finite étale group scheme V_ρ over ℚ". Faithful.
- **Verdict: SURVIVED.**

### `vRhoPointsEquiv` (YRho.lean:96, DS5c)
- **[T]** `{ h : Spec ℚ̄ ⟶ vRho D // h ≫ vRhoπ D = Spec.map (algebraMap ℚ ℚ̄) } ≃ (Fin 2 → ZMod N)`. The subtype = ℚ̄-points over the canonical ℚ→ℚ̄; RHS = `(ℤ/N)²`. Typechecks.
- **[S]** "ℚ̄-points biject with (ℤ/N)²"; GalQ-equivariance deferred to companion `vRhoPointsEquiv_equivariant` (T-F1b) — flagged.
- **[H]** Registered data (part of DS5). Equivariance is where `ρ` enters — correctly separated.
- **Verdict: SURVIVED** (data-sorry).

### `coord` (YRho.lean:104, real def) — **HYPOTHESIS GAP**
- **[H] MISSING `over_T` (the real defect).** The inner `sorry` must prove `(pointToTorsion x hx ≫ torsionIso.hom ≫ pullback.fst) ≫ vRhoπ D = Spec.map(algebraMap)`. Via `pullback.condition` this becomes `pointToTorsion x hx ≫ (torsionIso.hom ≫ pullback.snd) ≫ sT`. To finish one needs `torsionIso.hom ≫ pullback.snd = E.torsionπ N` — i.e. **exactly `RhoLevelStructure.over_T`** — which `coord` does NOT take as a hypothesis (it accepts a *bare* `torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT`). Without it the subtype obligation is **not dischargeable from `coord`'s current hypotheses**. Fix: add `(hOver : torsionIso.hom ≫ pullback.snd _ _ = E.torsionπ N)` to `coord`, or thread `torsionIso` bundled with `over_T`.
- **[H] `ht` is NOT unused (seed's guess rejected).** After the `over_T` step reduces the composite to `t ≫ sT`, the goal is `t ≫ sT = Spec.map(algebraMap)` — which is **precisely `ht`**. So `ht` is consumed at the final step (inside the `sorry`); removing it would break the proof. The seed's "remove ht" is **wrong**; the correct fix is "**add `over_T`**".
- **[T]** Otherwise well-formed: `vRhoPointsEquiv D ⟨…⟩ : Fin 2 → ZMod N`; the `rw` chain (`assoc`/`pullback.condition`) is valid up to the `sorry`.
- **Verdict: NEEDS-FIX** — add the `torsionIso.hom ≫ pullback.snd = E.torsionπ N` (`over_T`) hypothesis to `coord`; the inner `sorry` is otherwise not closable. (`ht` must stay.)

### `PairingCompatAt` (YRho.lean:121, DS5d relation, sorry-def)
- **[T]** Returns `Prop` via `sorry` — a *relation* data-sorry (register DS5d), discharged by T-F3 (Γ–Spec unfolding). Consumed only by `RhoLevelStructure.pairing_compat`. Correctly registered.
- **[H]** Takes `ht`, `x y`, `hx hy` — all needed to state the fibre relation.
- **[M]** Docstring: `e_N(x,y)=p(a₁b₂−a₂b₁)` — the symplectic form `a₁b₂−a₂b₁` matches the `ad−bc` orientation of `weilPairingEval_symplectic`. Convention-consistent.
- **Verdict: SURVIVED** (registered relation-sorry, DS5d).

### `RhoLevelStructure` (YRho.lean:138, structure) — `torsionIso, over_T, coords_additive, pairing_compat`
- **[H] Galois-equivariance clause (seed adjudication).** No explicit equivariance field. Correct: `torsionIso` is an iso of schemes **over T** (with `over_T`), hence a ℚ-morphism; equivariance on ℚ̄-points is **automatic** from scheme-morphism-ness over ℚ. ✓ No missing clause here.
- **[M/H] Geometric-points-only weakness (the real caveat).** `coords_additive` and `pairing_compat` are imposed **only on ℚ̄-points** (`t : Spec ℚ̄ ⟶ T`). Over a general/non-reduced ℚ-scheme T this does **not** pin the scheme-level group/pairing compatibility — the exact reply.md Q4 phenomenon. Docstring flags this ("strengthening to the scheme-level identity is ticket T-F3"). So the structure is a **deliberately-weaker surrogate**; downstream `yRho_representable`/`rhoLevel_relativelyRepresentable` inherit the caveat and are only faithful once T-F3 upgrades it.
- **[T]** `over_T : torsionIso.hom ≫ pullback.snd = E.torsionπ N` well-typed; `coord D sT torsionIso …` calls are consistent (though see `coord`'s own gap).
- **Verdict: SURVIVED-with-caveat** — design is sound and the group-compat-as-`coords_additive` is the intended spec; but the geometric-point-only quantification is load-bearing and must be upgraded (T-F3) before any bijection consuming it is faithful. Flag, don't reject (it is explicitly tracked).

### `rhoLevel_relativelyRepresentable` (YRho.lean:173, T-F6)
- **[H] ℚ-structure on T′ (seed).** `k : T' ⟶ T` arbitrary; T′ inherits ℚ via `k ≫ sT`, and the RHS uses `RhoLevelStructure D (k ≫ sT) (E.baseChange k)` — the inherited structure map is threaded correctly. ✓ No missing ℚ-structure.
- **[M]** Finite-étale `I` over T: char 0 ⟹ N invertible ⟹ étale automatic. `hN : 3 ≤ N` = rigidity (Loeffler 3.8.3 for Γ(N)). Isom^symp route matches **reply.md Q9 verbatim** ("represented by the corresponding symplectic Isom scheme Isom^symp(E[N], V_ρ̄)").
- **[T]** `E.baseChange k : EllipticCurve T'` real; equiv target well-typed.
- **[H]** Inherits `RhoLevelStructure`'s geometric-point caveat (see above) but structurally the relative-representability statement is correct.
- **Verdict: SURVIVED** (Q9 route; caveat inherited from `RhoLevelStructure`).

### `yRho_representable` (YRho.lean:190, T-F4) — **REJECTED**
- **[M] QUOTIENT RELATION FAR TOO COARSE (real defect).** Relation is `Nonempty (a.1.E ≅ b.1.E)` where `a b : Σ E : EllipticCurve T, RhoLevelStructure D sT E`. Confirmed from source: `EllipticCurve extends EllipticCurveGeom`, whose field is `E : Scheme.{u}` (total space). So `a.1.E ≅ b.1.E` is an isomorphism of **bare total-space schemes in `Scheme.{0}`** — it does **not** require: (i) the iso be **over T** (respect `π`); (ii) it be **pointed** (respect `zero`/group); (iii) it **carry the level structure** `a.2` to `b.2`. Consequence: for a fixed E, ALL level structures collapse (identity iso `E.E ≅ E.E` identifies `(E,α)` with `(E,α')` for every α≠α'), so the quotient forgets the level data entirely — it is at best a coarse curve-iso quotient, not the level-N moduli.
- **[S]** The cited source (decomposition.md F3, Buzzard p.33) says "**isomorphism classes of pairs (E, α)**". The stated relation contradicts its own quoted source.
- **[H/M] Fix.** Relation must be: `∃ f : a.1 ≅ b.1` an isomorphism **of elliptic curves over T** (pointed T-iso — respecting `π` and `zero`) such that **`f` transports the level structure**, i.e. `a.2` and `b.2.torsionIso` are compatible along the induced `E[N]`-iso (`b.2 = f_* a.2`). This is the levelled-groupoid iso on pairs `(E, α)` (cf. reply.md Q7's groupoid-valued problem).
- **[T]** The `∃ Y sY, SmoothOfRelativeDimension 1 sY ∧ IsAffineHom sY ∧ …` scaffold (smooth affine curve over ℚ) is correct; only the equivalence relation inside `Quot` is wrong.
- **Verdict: REJECTED** — relation `Nonempty (a.1.E ≅ b.1.E)` is a bare-scheme iso ignoring over-T-ness, pointing, and level-transport; too coarse (collapses all level structures). Replace with the pointed-over-T level-preserving iso on `(E,α)` pairs.

### `yRho_geometricallyIrreducible` (YRho.lean:201, T-F5, BB-IRR) — **NEEDS-FIX**
- **[M] STATEMENT FALSE AS UNIVERSALLY QUANTIFIED.** `Y, sY` are **arbitrary** bound variables with only `hY : SmoothOfRelativeDimension 1 sY`, and `D` is **unused**. The claim "every smooth-rel-dim-1 ℚ-scheme has irreducible base change to ℚ̄" is **false**: counterexample `Y = ℙ¹_ℚ ⊔ ℙ¹_ℚ` (smooth rel dim 1 over ℚ) has `Y ×_ℚ ℚ̄` = two disjoint components ⟹ `¬ IrreducibleSpace`. So the sorry can never be honestly discharged.
- **[H] Fix.** Bind `Y` to the moduli problem: either state it for the specific `Y` from `yRho_representable` (add the representability bijection as a hypothesis, tying `Y`/`sY` to `D`), or quantify `∃ Y … (representable ∧ IrreducibleSpace …)`. As-is, `D` dangling signals the missing link.
- **[T]** `IrreducibleSpace ↥(pullback sY (Spec.map (algebraMap ℚ ℚ̄)))` is the correct *rendering* of geometric irreducibility (irreducible after base change to ℚ̄); the type is fine — only the scoping is wrong.
- **[S]** BB-IRR "see 1980s" (Buzzard p.34) sanctions sorrying the *proof*; it does not sanction a *false statement*. A black box must still be true.
- **Verdict: NEEDS-FIX** — restrict `Y` to the representing twisted curve (tie to `D`/`yRho_representable`); the current universal quantification over all smooth `Y` is false (disjoint-union counterexample).

---

## Summary table

| # | Declaration (file:line) | Verdict |
|---|---|---|
| 1 | `weilPairing` (WP:42) | SURVIVED (DS4 data-sorry) |
| 2 | `weilPairing_over` (WP:46) | SURVIVED |
| 3 | `weilPairingEval` (WP:53) | SURVIVED |
| 4 | `weilPairingEval_add_left` (WP:67) | SURVIVED · QUOTE-MISSING (KM 2.8/Silv III.8.1a) |
| 5 | `weilPairingEval_self` (WP:76) | SURVIVED · QUOTE-MISSING (KM 2.8/Silv III.8.1b) |
| 6 | `weilPairingEval_nondegenerate` (WP:86) | SURVIVED (GME C.4 quote present) |
| 7 | `weilPairingEval_restrict` (WP:97) | SURVIVED (Q4 pin) |
| 8 | `weilPairingEval_mul` (WP:110) | SURVIVED — exponent `M` recomputed ✓ · QUOTE-MISSING (source) |
| 9 | `weilPairingEval_symplectic` (WP:124) | SURVIVED — `ad−bc` matches Q6 ✓ |
| 10 | `GalQ` (YR:46) | SURVIVED (instances via `krullTopology`/`AlgEquiv.aut`; doc-nit) |
| 11 | `card_rootsOfUnity_algClosureQ` (YR:50) | SURVIVED — shape = `hn` ✓ |
| 12 | `GaloisRepData` (YR:58) | SURVIVED — `det_cyclo`/`p_equivariant` same χ, consistent ✓ |
| 13 | `vRho` (YR:81) | SURVIVED (DS5 data-sorry) |
| 14 | `vRhoπ` (YR:84) | SURVIVED (DS5 data-sorry) |
| 15 | `vRhoπ_finite_etale` (YR:88) | SURVIVED |
| 16 | `vRhoPointsEquiv` (YR:96) | SURVIVED (DS5c data-sorry) |
| 17 | `coord` (YR:104) | **NEEDS-FIX** — add `over_T` hyp (`ht` must stay) |
| 18 | `PairingCompatAt` (YR:121) | SURVIVED (DS5d relation-sorry) |
| 19 | `RhoLevelStructure` (YR:138) | SURVIVED-with-caveat (geometric-points-only; T-F3 upgrade load-bearing) |
| 20 | `rhoLevel_relativelyRepresentable` (YR:173) | SURVIVED (Q9 route) |
| 21 | `yRho_representable` (YR:190) | **REJECTED** — quotient relation too coarse |
| 22 | `yRho_geometricallyIrreducible` (YR:201) | **NEEDS-FIX** — false as stated; bind `Y` to moduli problem |

## QUOTE-MISSING list (source-citation gaps — all consistent with the project's own KM-2.8 do-not-formalize-from-memory gate, PENDING-SOURCE(KM))
- **#4 `weilPairingEval_add_left`** — cites "KM 2.8.2; Silverman III.8.1(a)"; no verbatim quote in provided context. (Statement = standard bilinearity; correct.)
- **#5 `weilPairingEval_self`** — cites "KM 2.8; Silverman III.8.1(b)"; no verbatim quote. (Alternating; correct.)
- **#8 `weilPairingEval_mul`** — cites "Silverman III.8.4-type; KM 2.8"; no explicit `e_{NM}=e_N^M` in `decomposition-gme2.md` §C or elsewhere. **Exponent verified `M` by independent lattice recomputation**, so math stands; only the source quote is absent.

(For contrast, the following DO have verbatim support in the provided context: symplectic/`det_cyclo` ← reply.md Q6; `_restrict` ← reply.md Q4; `_nondegenerate` ← gme2 §C.4; `GaloisRepData`/`yRho_representable`/`yRho_geometricallyIrreducible`/`RhoLevelStructure`/`rhoLevel_relativelyRepresentable` ← decomposition.md F2/F3/F4 + reply.md Q9.)

## Adjudications explicitly requested by the seeds
- **`det_cyclo` inverse ambiguity:** No hidden χ vs χ⁻¹. mathlib `modularCyclotomicCharacter` is characterised by `g(ζ)=ζ^{χ(g)}` (= reviewer's χ); `det ρ = χ` is forced by `e(gv,gw)=e(v,w)^{det g}` + `e(σP,σQ)=e(P,Q)^{χ(σ)}` regardless of left/right GL₂-action. `p_equivariant` uses the **same** χ (same direction, no inverse) → mutually consistent with `det_cyclo`. **Consistent.**
- **`p_equivariant` exponent:** `((χσ : (ZMod N)ˣ) : ZMod N).val : ℕ` is exactly mathlib's `spec` form; `x ^ val` is the correct action transport (equals the ZMod-action since `Multiplicative (ZMod N)` is N-torsion). **Correct.**
- **`coord` `ht`:** NOT unused — needed at the final `t ≫ sT = Spec.map(algebraMap)` step; the actual missing ingredient is `over_T`. **Fix = add `over_T`, keep `ht`.**
- **`RhoLevelStructure` equivariance:** Automatic over ℚ (scheme-morphism-ness); no missing clause. Real caveat is the geometric-points-only quantification (T-F3).
- **`yRho_representable` relation:** Real defect — compares total spaces as bare schemes only. **REJECTED**; fix = pointed-over-T, level-transporting iso on `(E,α)` pairs.