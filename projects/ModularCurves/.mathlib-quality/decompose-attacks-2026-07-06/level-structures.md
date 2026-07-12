<!-- Adversarial /develop --decompose attack log, agent a1e5c9f396ae3d858, archived 2026-07-06 -->

All verification complete. Here is the adversarial verification report.

---

# ADVERSARIAL VERIFICATION REPORT — LevelStructure/{CartierDivisor,ExactOrder,Basic,Incidence}.lean

Method note: mathlib checks were done against the project's actual pin (`.lake/packages/mathlib`) by source-reading `RingTheory/Norm/Defs.lean`, `LinearAlgebra/Determinant.lean`, `AlgebraicGeometry/IdealSheaf/{Basic,Subscheme}.lean`, `Morphisms/{FlatRank,Etale,Separated,Smooth}.lean`, `RingTheory/TensorProduct/Free.lean`, plus `lean_local_search` (Scheme.Hom.ker, IdealSheafData, subschemeι, Scheme.Hom.finrank, Module.Dual, IsReduced, Algebra.norm lemmas) and `lean_run_code` exhaustive-enumeration checks. Project-side API (`asSection`, `baseChange`, `pointToTorsion`+simp lemma, `NIsInvertible`, `point_smul_eq_comp_mulBy`) audited in `EllipticCurve/{GroupLaw,Torsion}.lean`. DEF-1/2/3 (IsSeparated on incidence loci) confirmed present, not re-reported. DS4a's *sorry itself* not reported (registered); its **specification** is attacked.

## CartierDivisor.lean

### `RelEffCartierDiv` (CartierDivisor.lean:50)
- Attacks: [1] Over-generality (seed): structure is stated for arbitrary `π` with no smoothness/separatedness. For non-smooth `C` the name is a misnomer — in `C = Spec k[x,y]/(xy)`, `V(x,y)` is finite+flat+lfp closed but its ideal is *not* invertible, so it is not a Cartier divisor; "divisors" over `π = 𝟙 S` degenerate to arbitrary flf closed subschemes of `S`. Harm audit over all in-repo consumers: every consumer either supplies smooth+separated hypotheses (incidence loci), an elliptic curve (`IsSubgroup`, subgroup locus), or is itself flagged below (`sectionsDivisor_degree` — the one place the over-generality already produced a false statement). → benign for the structure, charged to the spec.
- [2] Hypothesis strength vs KM: KM 1.2.3's equivalence (finite flat ⟺ proper ECD) holds only for smooth curves; the file never asserts it (T-D1, gap AG-LB registered), and the working def has the *advantage* that KM 1.3.x's "proper over S" is automatic (finite ⟹ proper). → faithful working form.
- [3] Discharge check: `Scheme.IdealSheafData` (structure), `subscheme`/`subschemeι` (defs), `IsFinite`/`Flat`/`LocallyOfFinitePresentation` all verified present at the pin; `ker_subschemeι : I.subschemeι.ker = I` gives the closed-subscheme dictionary. finite+flat+lfp = finite locally free is Stacks 02KA/02KB, matching `FlatRank`'s docstring.
- [4] Dedup: no `EffectiveCartier`/`CartierDivisor` anywhere in mathlib at this pin; no duplicate in other AINTLIB projects (grep clean).
- Verdict: **SURVIVED** (over-generality benign given T-D1 registration; keep consumers hypothesised).

### `RelEffCartierDiv.degree` (CartierDivisor.lean:63)
- Attacks: [1] Junk-value: `Scheme.Hom.finrank` (FlatRank.lean:89) is a total function, honest/locally-constant exactly under finite+flat+lfp — all three carried by the structure. → honest.
- [2] The `haveI := D.finite/D.flat` lines are inert (the def takes no instance arguments) and `lfp` is not passed — cosmetic only, no elaboration risk.
- [3] Source drift: KM's degree = rank of the flf module `O_D` at `s` ✓; edge `s` with empty `D`-fibre gives 0, consistent with the empty divisor having degree 0.
- Verdict: **SURVIVED**.

### `RelEffCartierDiv.sectionsDivisor` (CartierDivisor.lean:72) — DS4a interface
- Attacks: [1] Fin-indexing/multiplicity: duplicates allowed (needed for `[P]+[2P]+…` with collisions); `n = 0` gives the unit-ideal empty divisor, consistent with degree 0. → correct interface.
- [2] Docstring-pin vs arbitrary `π`: "(closed-immersion) sections" is false without `[IsSeparated π]` (sections are closed immersions only for separated morphisms), and the ideal-product construction violates its own degree spec on non-smooth `C` (see next item). The data-sorry is registered, but the *pin* (docstring + spec) is incoherent for bad `π`.
- [3] Type-correctness of the section subtype `{z // z ≫ π = 𝟙 S}` ✓ matches KM's `C(S)`.
- Verdict: **NEEDS-FIX** — scope the docstring/construction to KM 1.2.1's standing hypotheses (separated + smooth rel. dim. 1), or hypothesise the spec (below); as pinned today T-D3 cannot deliver both docstring and spec.

### `sectionsDivisor_degree` (CartierDivisor.lean:76)
- Attacks: [1] Counterexample (unsatisfiable by ANY data filling): take `C = S = Spec k`, `π = 𝟙`, `n = 2`, `P = ![𝟙, 𝟙]`. The only closed subschemes of `Spec k` have degree 0 or 1; no `RelEffCartierDiv 𝟙` of degree 2 exists, so the statement is false however DS4a is constructed. → statement FALSE.
- [2] Counterexample to the docstring construction: nodal `C = Spec k[x,y]/(xy)/Spec k`, `P₁ = P₂ =` the node; ideal product `(x,y)²` gives `dim_k k[x,y]/(xy,x²,y²) = 3 ≠ 2`.
- [3] Source drift: KM 1.2.2 is proved under KM 1.2.1's standing assumptions (smooth separated relative curve) — the statement dropped them entirely (contrast: `exists_incidenceLocusLE/EQ` carry exactly these after DEF-1/2).
- Verdict: **REJECTED** — add `[IsSeparated π]` + `SmoothOfRelativeDimension 1 π` (KM 1.2.1 standing hypotheses). All in-repo uses (`orderDivisor`, `IsFullLevel`) are over elliptic curves and satisfy them.

### `AlgHom.sectionBaseChange` (CartierDivisor.lean:89)
- Attacks: [1] Formula: `rid ∘ map(id,P)` sends `a ⊗ b ↦ a·P(b)` — the correct base-changed section `(Pᵢ)_A`. [2] Edge: `A = 0` trivial; universe restriction `A : Type u` benign (KM's universal case lives in `u`). [3] Namespace: resolves to `ModularCurves.AlgHom.sectionBaseChange`, so `P.sectionBaseChange` dot-notation will not fire — style only.
- Verdict: **SURVIVED**.

### `IsFullSetOfSectionsAlg` (CartierDivisor.lean:104) — the norm-junk seed
- Attacks: [1] Junk-value counterexample search (CONFIRMED at source): `LinearMap.det = if ∃ s : Finset M, Nonempty (Basis s A M) then … else 1` (Determinant.lean:178–180) and `Algebra.norm = det ∘ lmul` with `norm_eq_one_of_not_exists_basis` (Norm/Defs.lean:61–72); mathlib's own `norm_zero` is guarded by `[Module.Free][Module.Finite]` (Norm/Basic.lean:90). A finite *projective non-free* module has no basis, so `Algebra.norm ≡ 1` there. Taking `A = R` in the `∀ A` quantifier: for `B` flf-but-not-free (a real case in the intended applications — e.g. `B = O(N·[0])` over a Dedekind `R` where `ω_E` is a nontrivial line bundle, so `B ≅ R ⊕ ω ⊕ … ⊕ ω^{N-1}` non-free, with the legitimate full set `P₁ = … = P_N = 0`), the condition at `f = 0` reads `1 = ∏ᵢ Pᵢ(0) = 0` — false in nontrivial `R`. **The definition is falsely strong exactly on the locally-free-non-free stratum KM 1.8.2 covers.**
- [2] Positive half (seed's key question, answered): for `B` finite **free** over `R`, `A ⊗[R] B` is finite free over `A` for *every* `R`-algebra `A` (`Algebra.TensorProduct.basis` + `instFree`, TensorProduct/Free.lean — verified present), and since the det branch is a propositional classical `if` (no instance resolution involved), the norm is honest for every quantified `A`. Under `[Module.Free R B] [Module.Finite R B]` the `∀A` form is fully faithful to KM 1.8.2 and equivalent to the universal case by KM 1.8.4. So `A ⊗ B` flf over `A`: yes always; mathlib computing it correctly: **only when a basis exists**, i.e. free, not merely locally free.
- [3] Edge cases: `n = 0`, `B = 0`: norm on the zero module honestly 1 = empty product — correctly says the empty family is full for the empty scheme. Rank/`n` mismatch: `f = λ ⊗ 1` over `A = R[λ]` forces `λ^{rank B} = λ^n`, so both sides can only hold when rank = n — no accidental truths. `R = 0`: vacuous.
- [4] Source drift: KM quantifies over affine base changes `Spec A → Spec R` with `Z_A` flf/`A` (automatic) and uses the honest glued determinant; the Lean transcription silently substitutes a basis-guarded norm — drift is precisely the non-free stratum of [1]. The header's claim (lines 26–28, 95–103) "honest definition quantified over base changes (equivalent … by KM 1.8.4)" is true only given freeness.
- Verdict: **NEEDS-FIX** — add `[Module.Free R B] [Module.Finite R B]` to the definition (or caveat it and force all consumers, including T-D4's globalisation and T-D30's equivalence, to work over a free/trivialising affine cover — never on arbitrary affines). Sole current consumer `isFullSetOfSectionsAlg_iff_fields` already carries Free+Finite, so the fix is non-breaking.

### `isFullSetOfSectionsAlg_iff_fields` (CartierDivisor.lean:113)
- Attacks: [1] Hypothesis necessity (non-reduced `R`): `R = k[ε]`, `B = R[t]/(t²)`, `P₁ = (t ↦ 0)`, `P₂ = (t ↦ ε)`: over every field `K` both sections coincide and `Norm(a+bt) = a² = ∏ f(Pᵢ)` — RHS holds; over `R`, `∏ f(Pᵢ) = a(a+bε) = a² + abε ≠ a² = Norm` — LHS fails. `IsReduced` is genuinely needed ✓ matches KM 1.9.2's "S reduced".
- [2] `[Module.Free R B]` is stronger than KM's "finite locally free" — but forced by the norm-junk finding above; acceptable, with the drift noted (KM's statement in the projective case is currently *inexpressible* through `Algebra.norm`).
- [3] RHS quantifies over all field `R`-algebras vs KM's geometric points (alg. closed residue extensions): the two criteria are interderivable given the trivial base-change direction of the definition — equivalent theorem, mild phrasing drift only.
- [4] Name resolution: `IsReduced` could collide with `AlgebraicGeometry.IsReduced` (file `open AlgebraicGeometry`) — only the ring class elaborates at `R : Type u`, so resolution is unambiguous.
- Verdict: **SURVIVED**.

## ExactOrder.lean

### `EllipticCurve.Section` (ExactOrder.lean:46)
- Attacks: [1] `E.Point (𝟙 S)` is exactly `E(S)` ✓. [2] `AddCommGroup` available via the real (sorry-free) `pointAddCommGroup` — verified in GroupLaw.lean:115. [3] `abbrev` (reducible) so all `Point`-level API applies — no API split.
- Verdict: **SURVIVED**.

### `Point.pull` (ExactOrder.lean:49)
- Attacks: [1] Formula `t ≫ P.1` with the associativity proof = restriction along `t`, KM's `P_k` ✓. [2] Group-hom property is not stated, but every statement uses `pull` only inside smul-equations *in the group `E.Point t`*, which is literally KM's "`a·P_k` in `C(k)`" — faithful at statement level; the hom lemma is proof-side work. Near-duplicate of `Point.restrict` (GroupLaw.lean:127) modulo `comp_id` — dedup nit only. [3] Edge `T = ∅`: `Point t` is a singleton, trivial group — no degeneracy.
- Verdict: **SURVIVED**.

### `RelEffCartierDiv.IsSubgroup` (ExactOrder.lean:55)
- Attacks: [1] Encoding: `∃ H : AddSubgroup, ∀ P, P ∈ H ↔ factors` pins `H`'s carrier to the factoring set — exactly KM 1.3.6's "the subset `D(T)` of the group `C(T)` is in fact a sub-group" (verbatim quote in hand, D1). `D(T)` is an honest subset since factorization through a mono is unique. [2] Hypothesis strength: KM 1.3.6 assumes `D` proper — automatic (finite) in the working def; smooth group-curve supplied by `E`. [3] Edge `T = ∅`: `Point g` singleton, `H = ⊤` works. [4] Per-`(T,g)` quantification with no cross-`T` compatibility — same as KM; the set-pinning makes functoriality automatic downstream.
- Verdict: **SURVIVED**.

### `Section.orderDivisor` (ExactOrder.lean:61)
- Attacks: [1] Off-by-one (seed): `a : Fin N ↦ ((a:ℕ):ℤ)+1` — verified by `decide` (N=5: `[1,2,3,4,5]`), so the family is `P, 2P, …, NP` exactly, matching KM 1.4.1's `[P]+[2P]+⋯+[NP]`. [2] `N = 0` (no `NeZero` here): empty divisor; junk but gated at `HasExactOrder`. [3] Coefficients as ℤ-smul are pinned to `[n]` by spec `point_smul_eq_comp_mulBy` (T-A6d, registered). [4] Built on DS4a over an elliptic curve — smooth+separated+proper, so the (to-be-repaired) degree spec is legitimately applicable here.
- Verdict: **SURVIVED**.

### `Section.HasExactOrder` (ExactOrder.lean:68)
- Attacks: [1] Verbatim KM 1.4.1 match ✓ (D2 quote). [2] Caution 1.4.3 respected: it is a Prop in `N`, never "the order" — over `𝔽_p` the zero section will correctly have exact order `pⁿ` for all `n`; not a bug. [3] `N = 1` sanity: `[P]` a subgroup ⟺ `P = 0` ✓. [4] `[NeZero N]` excludes the degenerate empty divisor ✓.
- Verdict: **SURVIVED**.

### `HasExactOrder.smul_eq_zero` (ExactOrder.lean:74)
- Attacks: [1] Verbatim KM 1.4.2 with the Oort–Tate input registered (BB-DELIGNE/stream OT) ✓. [2] ℤ- vs ℕ-smul: equivalent ✓. [3] `N = 1`: exact order 1 ⟹ `P = 0` ✓ consistent.
- Verdict: **SURVIVED**.

### `hasExactOrder_iff_geometric` (ExactOrder.lean:81)
- Attacks: [1] Source drift (KM 1.4.4's *standing hypothesis*): KM states "(1)⇔(3)" under "Let `P ∈ C(S)` be a point **killed by N**". The Lean statement drops it, compensating only with a per-geometric-point `N•P_t = 0` — which is strictly weaker over non-reduced bases. decomposition.md D5 itself flagged this as "attack pending".
- [2] Counterexample (executes the pending attack — the iff is FALSE as stated): `S = Spec ℚ̄[ε]`, `E` the constant curve, `P₀ ∈ E(ℚ̄)` of exact order `N ≥ 2` (or even `N=1` with `P₀ = 0`). Lifts of `P₀` form a torsor under `Lie(E) ≅ ℚ̄` inside `E(S) → E(ℚ̄)`, and `N•(P̃)` sweeps *all* lifts of `0` as the lift varies (N invertible), so choose `P̃` with `N•P̃ = v ≠ 0` in the tangent kernel. Every alg.-closed-field point `t : Spec k → S` kills `ε`, so `pull P̃ = (P₀)_k`: RHS holds. LHS fails: exact order would force `N•P̃ = 0` by KM 1.4.2 (= this file's own `smul_eq_zero` spec); for `N=2` also directly — the zero section cannot factor through `[P̃] ⊔ [2P̃]` (connected base, both branches nonzero).
- [3] Hypothesis check `NIsInvertible`: `IsUnit (N : Γ(S,⊤))` (Torsion.lean:44) — correct notion, and satisfied by `ℚ̄[ε]`, so invertibility does not rescue the statement.
- [4] RHS shape vs KM (3): "N least positive integer killing `P_k`" = `N•P_t = 0 ∧ ∀ 0<a<N, a•P_t ≠ 0` ✓ faithful *given* the standing hypothesis.
- Verdict: **REJECTED** — add the hypothesis `(N : ℤ) • P = 0` (KM's standing assumption) to the theorem; the iff is false without it.

### `hasExactOrder_iff_etale` (ExactOrder.lean:90)
- Attacks: [1] Same missing standing hypothesis as above; KM 1.4.4 (4) is stated for `P` killed by `N`.
- [2] Counterexample: same `S = Spec ℚ̄[ε]`, `N = 2`, `P̃` with `2P̃ = v ≠ 0`: the sections `P̃` and `2P̃` have distinct reductions (`P₀ ≠ 0`), hence disjoint supports, so `[P̃] + [2P̃] ≅ S ⊔ S` is finite étale — RHS true; LHS false (zero-section factoring argument, no Oort–Tate needed). Iff FALSE.
- [3] RHS well-formedness: `Etale` (class, Morphisms/Etale.lean:41) exists; "finite étale" = `Etale` + structural finiteness of `D` ✓ no strength lost.
- Verdict: **REJECTED** — same fix: hypothesis `(N : ℤ) • P = 0`.

## Basic.lean

### `IsNaiveFullLevel` (Basic.lean:43)
- Attacks: [1] The `k[ε]`-attack does NOT go through: the global killing clauses `(N:ℤ)•P = 0 ∧ (N:ℤ)•Q = 0` are present (this is exactly what the Γ₁ defs below lack). [2] Generation clause: closure of `{pull P, pull Q}` sits inside `E[N](k)` automatically (pulls are killed), so "⊆ + ⊇" = Loeffler 3.8.1's "generating `E[N]` in every fibre" ✓ verbatim quote in hand. [3] Edges: `N = 1` forces `P = Q = 0`, condition trivially true — correct (`Γ(1)` structure exists); char `p ∣ N` at a geometric point: definition remains meaningful (and deliberately diverges from Drinfeld — the iff below is gated by invertibility). [4] Quantifier `∀ k [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S)` = geometric points ✓.
- Verdict: **SURVIVED**.

### `IsNaiveGammaOne` (Basic.lean:52)
- Attacks: [1] Asymmetry audit: unlike `IsNaiveFullLevel`, there is NO global `(N:ℤ)•P = 0` clause — only fibrewise killing. The docstring's claim "For `N` invertible this coincides with the Drinfeld notion" is false: the `Spec ℚ̄[ε]` counterexample above satisfies `IsNaiveGammaOne` but not `IsGammaOne`.
- [2] Consumer blast radius (checked by grep): `Moduli/Representability.lean:114` uses it as the object clause of `gammaOneNaiveProblem` — the Y₁(N) moduli functor. Without global killing that functor strictly contains `h_{Y₁(N)}` (every family classified by Y₁(N) has `N•P_univ = 0` globally, hence so do all its pullbacks; `(E, P̃)/ℚ̄[ε]` is in the functor but classified by nothing), so `gammaOneNaive_representable` (T-E7) becomes unprovable as stated.
- [3] Source drift: "the right-hand side of KM 1.4.4" is only defined under KM's standing "killed by N"; Loeffler's E3 route also imposes `NP = 0` through the Tate-normal construction (the relation cutting out Y₁(N) *is* `NP = 0`).
- Verdict: **NEEDS-FIX** — prepend `((N : ℤ) • P = 0) ∧` (mirrors `IsNaiveFullLevel`); this simultaneously repairs `isGammaOne_iff_naive` and T-E7.

### `IsGammaOne` (Basic.lean:59)
- Attacks: [1] Definitional alias of `HasExactOrder` — inherits its verified faithfulness to KM 1.4.1. [2] No junk, no hypotheses to weaken. [3] KM 3.2 locator: not in hand (preview stops at 1.9) — acceptable since the content is KM 1.4.1, but the Ch. 3 quote-gate stays open.
- Verdict: **SURVIVED** (KM 3.2 on the quote-missing list).

### `torsionIdeal` (Basic.lean:65)
- Attacks: [1] Register-rule check: it is a *data*-sorry consumed by `IsFullLevel` via bare equality, yet **no pinning specification theorem exists anywhere in the skeleton** (plan.md's register rule (iii) requires one; the table only names T-B3a as the construction ticket). As it stands, the truth-value of every `IsFullLevel` statement is unconstrained by the register's own rules.
- [2] Constructive kill (discharge check): mathlib already has `Scheme.Hom.ker : (X ⟶ Y) → Y.IdealSheafData` and the adjunction `ker_subschemeι` (IdealSheaf/Subscheme.lean:567), and the project has `torsionι` (Torsion.lean:54) — so `torsionIdeal N := (E.torsionι N).ker` is definable TODAY with no sorry; the closed-immersion fact (T-B3) is then only needed for the comparison `subscheme ≅ E.torsion N`, which becomes the natural pin.
- [3] Edge `N = 0`: `torsion 0 = ker [0] = E` — harmless, consumers gate `NeZero`.
- Verdict: **NEEDS-FIX** — replace the data-sorry by `(E.torsionι N).ker` (or add a pinning spec `(E.torsionIdeal N).subscheme ≅ E.torsion N` compatible with `subschemeι`/`torsionι`).

### `IsFullLevel` (Basic.lean:70)
- Attacks: [1] Enumeration (seed): verified exhaustively by `decide`: for `N = 3` the map `i : Fin 9 ↦ (i%3, i/3)` lists all of `{0,1,2}²` in order, and for `N = 4` all 16 pairs `Nodup` — so the `Fin (N²)` family enumerates `(ℤ/N)²` bijectively, *including* `(0,0) ↦ 0•P + 0•Q = 0` — matching GME (2.46)'s sum over ALL `x ∈ (ℤ/N)²` (with `φ(0) = 0`); degree `N²` = rank `E[N]` requires the zero pair, and it is there.
- [2] Coefficient normalisation: representatives `0..N−1` are canonical; the killing clause makes any representative choice mathematically irrelevant; killing is also *redundant* given the divisor equality (`[P] ≤ Σ ≤ E[N]` via ideal-product monotonicity) — harmless, consistent with "P, Q ∈ E[N](S)".
- [3] char `p ∣ N` sanity (definition must not exclude Drinfeld phenomena): supersingular `E/𝔽̄_p`, `P = Q = 0`, `N = p`: divisor `= p²[0] = V(t^{p²}) = E[p]` (height-2 `[p]`), so `(0,0)` is correctly a Γ(p)-structure; ordinary case with `P₀` generating the étale part also comes out right. The definition supports the arbitrary-base register as intended.
- [4] Pin gap: the RHS `E.torsionIdeal N` is the unpinned data-sorry above — until fixed, `IsFullLevel` is formally unconstrained (charged to `torsionIdeal`).
- [5] Source drift: the definition-of-record form here is divisor-equality; KM 3.1's official phrasing ("full set of sections of E[N]") and the bridging equivalence (KM 1.10.x, *outside* the in-hand §§1.1–1.9) are both PENDING-SOURCE — the docstring's "i.e." asserts the bridge without a quote.
- Verdict: **SURVIVED** (conditional on the `torsionIdeal` fix; KM 3.1 + the full-sets/divisor bridge on the quote-missing list).

### `isFullLevel_iff_naive` (Basic.lean:80)
- Attacks: [1] Non-reduced-base attack: blocked — both sides carry global killing (`IsFullLevel` clause / `IsNaiveFullLevel` clause), and for `N` invertible `E[N]` and the section-divisor are étale, so fibrewise agreement rigidifies over nilpotents. [2] Direction audit: → uses étaleness of the divisor to get fibrewise distinctness ⟹ generation; ← is the KM 1.8.3-style disjointness/exhaustion argument — both KM-supported. [3] Edge `N = 1`: both sides collapse to `P = Q = 0` (+ trivially true divisor equality) ✓. [4] KM 3.7 quote not in hand (statement cited via Loeffler) — quote-gate open.
- Verdict: **SURVIVED** (KM 3.7 quote missing).

### `isGammaOne_iff_naive` (Basic.lean:86)
- Attacks: [1] RHS = `IsNaiveGammaOne` (no global killing) ⟹ inherits the `Spec ℚ̄[ε]` counterexample of `hasExactOrder_iff_geometric` verbatim: RHS true, LHS false. [2] Even repairing only the theorem (adding `(N:ℤ)•P = 0` as hypothesis) leaves the T-E7 consumer broken — the def-level fix is the right one. [3] Cross-check: with the def-level fix both this and T-D9's KM 1.4.4 (1)⇔(3) become the true statement.
- Verdict: **REJECTED** as stated — fixed automatically by the `IsNaiveGammaOne` repair (or add the killing hypothesis to the theorem).

### `IsGammaZero` (Basic.lean:94)
- Attacks: [1] char `p ∣ N` (seed): the geometric surrogate is WRONG there, and not merely weaker: `G = Ker F ⊂ E` supersingular over `𝔽̄_p` (`N = p`) is KM-cyclic — the zero section is a *Drinfeld* generator, `Σ_{a=1}^{p}[a·0] = p[0] = Ker F` (KM 1.4.3) — but `geometricallyCyclic` demands a point of *naive* exact order `p` in `E(k̄)`, and `E[p](k̄) = 0`, so `IsGammaZero` excludes a legitimate KM Γ₀(p)-structure. Also the generation clause tests points, not divisor equality — vacuous on infinitesimal `G`.
- [2] Docstring justification audit: "fppf covers of a field split" is actually TRUE over algebraically closed fields (a nonzero f.p. algebra over `k̄` has a `k̄`-point, and divisor equality descends along the section) — so the *stated reason* is not the flaw; the flaw is substituting naive order for Drinfeld order in the generator condition. With the Drinfeld phrasing (`(orderDivisor P₀ N).ideal = (G.baseChange t).ideal` over `k̄`) the geometric form WOULD be honestly equivalent over geometric points — and that phrasing is already expressible with this file's vocabulary.
- [3] Gate audit: T-D10 (fppf-local definition of record) is registered, and plan.md forbids any Γ₀-representability through the surrogate — the process fence exists; the defect is the docstring's unqualified "equivalent for our purposes over geometric points".
- [4] Remaining fields: `isSubgroup` = KM 1.3.6 ✓, `degree_eq` = rank `N` ✓ (KM 1.4.1 cyclic-subgroup quote in hand, D9).
- Verdict: **NEEDS-FIX** — either upgrade `geometricallyCyclic`'s `P₀`-condition to the Drinfeld divisor-equality form, or caveat the docstring: surrogate agrees with KM 3.4 only where `N` is invertible; strictly wrong for char `p ∣ N` (Ker F counterexample); definition of record = T-D10.

## Incidence.lean

### `sectionVanishingIdeal` (Incidence.lean:53)
- Attacks: [1] Non-free trap (seed): `M = ℤ/2` over `ℤ`: `Module.Dual ℤ (ℤ/2) = 0`, so the ideal is `⊥` for every `σ`, declaring `σ = 1 ≠ 0` "vanishing everywhere" — junk for non-projective `M` (correct, since that zero locus isn't even closed). [2] Projective case (the case the plan's localize-and-glue step D-inc.2(b) actually hits on affine opens): `M` a direct summand of `R^n` ⟹ restricted coordinate functionals separate and detect `σ ⊗ 1 = 0` after any base change, and Dual commutes with localization for f.p. modules — the definition IS correct for all finite locally free `M`, not just free (contrast with the `Algebra.norm` situation). [3] Edge `M = 0`: ideal `⊥`, locus everything ✓. Free case: ideal = span of the `d′` basis-coordinates ✓ = KM 1.3.5's `V(r₁,…,r_{d′})` (mechanism transcribed in decomposition-km1 D-inc.2).
- Verdict: **SURVIVED** (add a one-line docstring caveat "meaningful only for `M` projective/locally free" if desired).

### `sectionVanishingIdeal_spec` (Incidence.lean:59)
- Attacks: [1] Tautology check: RHS `sectionVanishingIdeal R M σ ≤ RingHom.ker f` unfolds by `Ideal.span_le` to `∀ φ, φ σ ∈ ker f` — literally the LHS. The theorem is a hypothesis-free one-liner; `[Module.Finite R M] [Module.Free R M]` are unused. [2] Intent mismatch: T-D13 per decomposition-km1 D-inc.2(a) is "coordinates **w.r.t. a basis** suffice" — the finitely-many-equations content (`deg D′` equations, consumed by KM 1.3.4/1.3.5/1.3.7's counts). The stated form never mentions a basis, so a worker can "discharge" T-D13 without producing the load-bearing lemma, and the incidence chain silently loses its equation-count engine. [3] Discharge check: `Module.Dual` (abbrev, Dual/Defs.lean:62), `Ideal.span`, `Basis.coord` all present — the intended statement is stateable today.
- Verdict: **NEEDS-FIX** — restate with a basis, e.g. `theorem sectionVanishingIdeal_eq_span_coord (b : Basis ι R M) (σ : M) : sectionVanishingIdeal R M σ = Ideal.span (Set.range fun i => b.coord i σ)` (plus, if wanted, the `f`-version quantified over `b.coord i σ` only).

### `RelEffCartierDiv.baseChange` (Incidence.lean:77)
- Attacks: [1] Pullback orientation: `pullback.snd D.ι (pullback.fst π t) : D ×_S T ⟶ C ×_S T` (via `D ×_C C_T = D ×_S T`), its `.ker` is an `IdealSheafData` on `C_T`, and the structure morphism `pullback.snd π t` is definitionally `(E.baseChange t).π` where consumed (GroupLaw.lean:136–137) — all coherent. [2] Discharge: `Scheme.Hom.ker` real (IdealSheaf/Basic.lean); `ker_subschemeι` adjunction gives back the subscheme; `IsClosedImmersion` base-change stability makes the ker honestly the image ideal — the three sorried Prop fields are exactly mathlib-stable properties (T-D12) ✓. [3] Edge `T = ∅`: degenerates cleanly. [4] Missing-at-skeleton: degree-preservation (KM 1.2.9) and functoriality — registered as DS4a spec + T-D12; acceptable.
- Verdict: **SURVIVED**.

### `RelEffCartierDiv.IsSubdivisor` (Incidence.lean:87)
- Attacks: [1] Factorization-through-closed-immersion ⟺ ideal containment (mathlib dictionary) ⟺ KM 1.3.1's `g ∣ f` in the smooth case; orientation (`IsSubdivisor D' D` = `D' ≤ D`) consistent with every use site. [2] For bad `π` containment ≠ divisibility, but all consumers carry smooth+separated. [3] Prop-level `∃ j` with automatic uniqueness (mono) ✓.
- Verdict: **SURVIVED**.

### `exists_incidenceLocusLE` (Incidence.lean:95) and `exists_incidenceLocusEQ` (Incidence.lean:103)
- Attacks: [1] Hypothesis strength vs KM 1.2.1 standing assumptions: `[IsSeparated π]` + `SmoothOfRelativeDimension 1 π` now present (DEF-1/2, confirmed); `D′` properness automatic (finite). [2] Omissions vs KM 1.3.4/1.3.5 (uniqueness of `Z`; formation commutes with base change): both are *derivable* from the stated `∀ T` property (two closed subschemes with identical factoring functors are equal — take `T` = each subscheme), so no content is lost; equation-counts (`deg D′` / `deg D`) are docstring-only — flag that KM 1.3.7's `1 + d + d²` count will eventually need them as lemmas. [3] EQ's RHS = mutual `IsSubdivisor` = equality of closed subschemes ✓ KM 1.3.5 verbatim in hand. [4] Edge: `D′` = degree-0 (empty) divisor ⟹ `Z = S` — statements remain true/consistent. [5] `hsm` passed as an explicit term of a class — proofs will need `haveI`; style only.
- Verdict: both **SURVIVED**.

### `exists_subgroupLocus` (Incidence.lean:117)
- Attacks: [1] KM 1.3.7 hypotheses (smooth group-curve, `D` proper): supplied by `E : EllipticCurve` + structural finiteness ✓; verbatim quote (with proof) in hand. [2] RHS relativization `(D.baseChange t).IsSubgroup (E.baseChange t)` typechecks by the defeq noted above and is the correct "universal for `D` is a subgroup after base change" form; formation-commutes again derivable. [3] Three-conditions decomposition (`[e] ≤ D`, `D = inv*D`, `[m(P₁,P₂)] ≤ D_W`) is proof-plan (D-inc.3), not smuggled into the statement ✓.
- Verdict: **SURVIVED**.

### `exists_exactOrderLocus` (Incidence.lean:128)
- Attacks: [1] Orientation (seed): `Z ⊆ E[N]`, and the ⟺ is "classifying map `pointToTorsion P hP : T ⟶ E[N]` factors through `Z` ⟺ the point has Drinfeld exact order over `T`" — the correct KM 1.6-style universal property on the Hom-scheme (`Hom(ℤ/N, E) = E[N]`), not on `S` or `T`. [2] Coverage: every `g : T ⟶ E.torsion N` equals `pointToTorsion` of its induced killed point (`pullback.lift` + `hom_ext` on the kernel square, Torsion.lean:50–66), so quantifying over `(t, P, hP)` is the full universal property. [3] Coherence of the two "killed by N" encodings: morphism-level `hP` here vs smul-level in `HasExactOrder` — bridged by the registered spec `point_smul_eq_comp_mulBy` (T-A6d). [4] `asSection`/`baseChange` audit: real constructions (GroupLaw.lean:135–153), and `HasExactOrder (E.baseChange t)` is exactly "exact order as a section of the base-changed curve" ✓. [5] Edge `N = 1`: `E[1] ≅ S`, `Z` = everything, both sides ⟺ `P = 0` ✓.
- Verdict: **SURVIVED** (verbatim KM 1.6.2/1.6.3 statement quotes still to be pulled — see list).

### `exists_fullLevelLocus` (Incidence.lean:139)
- Attacks: [1] Hom-scheme: `pullback (torsionπ N) (torsionπ N)` = `E[N] ×_S E[N]` = `Hom((ℤ/N)², E)` ✓; the `pullback.lift … (by simp)` side condition is discharged by the real simp lemma `pointToTorsion_torsionπ` (Torsion.lean:68–72). [2] A-structure vs A-generator disambiguation: RHS `IsFullLevel` = divisor-equality-with-`E[N]` = KM's A-*generator* condition (1.6.5 EQ-locus route in decomposition-km1 D-inc.4), which is the correct notion for `[Γ(N)]`; the docstring's "KM 1.5–1.6" is loose but the mathematics lines up. [3] Redundancy: `hP`/`hQ` + `IsFullLevel`'s internal killing clauses overlap — harmless. [4] Inherits the `torsionIdeal` pin gap through `IsFullLevel`. [5] Edge `N = 1`: locus = everything, RHS trivially true for the forced `P = Q = 0` ✓.
- Verdict: **SURVIVED** (conditional on `torsionIdeal` fix; KM 1.6.5/3.1 quotes pending).

---

## Summary table

| Declaration | File:line | Verdict |
|---|---|---|
| `RelEffCartierDiv` | CartierDivisor:50 | SURVIVED (T-D1 caveat registered) |
| `degree` | CartierDivisor:63 | SURVIVED |
| `sectionsDivisor` (DS4a) | CartierDivisor:72 | NEEDS-FIX (scope pin to KM 1.2.1 hyps) |
| `sectionsDivisor_degree` | CartierDivisor:76 | **REJECTED** (false for arbitrary π; add IsSeparated + SmoothOfRelativeDimension 1) |
| `AlgHom.sectionBaseChange` | CartierDivisor:89 | SURVIVED |
| `IsFullSetOfSectionsAlg` | CartierDivisor:104 | **NEEDS-FIX** (norm junk: false for flf-non-free B; add Free+Finite) |
| `isFullSetOfSectionsAlg_iff_fields` | CartierDivisor:113 | SURVIVED |
| `Section` | ExactOrder:46 | SURVIVED |
| `Point.pull` | ExactOrder:49 | SURVIVED |
| `RelEffCartierDiv.IsSubgroup` | ExactOrder:55 | SURVIVED |
| `Section.orderDivisor` | ExactOrder:61 | SURVIVED |
| `Section.HasExactOrder` | ExactOrder:68 | SURVIVED |
| `HasExactOrder.smul_eq_zero` | ExactOrder:74 | SURVIVED |
| `hasExactOrder_iff_geometric` | ExactOrder:81 | **REJECTED** (missing "killed by N"; ℚ̄[ε] counterexample) |
| `hasExactOrder_iff_etale` | ExactOrder:90 | **REJECTED** (same; S ⊔ S counterexample) |
| `IsNaiveFullLevel` | Basic:43 | SURVIVED |
| `IsNaiveGammaOne` | Basic:52 | **NEEDS-FIX** (add global (N:ℤ)•P = 0; breaks T-E7 otherwise) |
| `IsGammaOne` | Basic:59 | SURVIVED |
| `torsionIdeal` | Basic:65 | **NEEDS-FIX** (unpinned data-sorry; define as `(E.torsionι N).ker`) |
| `IsFullLevel` | Basic:70 | SURVIVED (indexing verified; pin via torsionIdeal) |
| `isFullLevel_iff_naive` | Basic:80 | SURVIVED |
| `isGammaOne_iff_naive` | Basic:86 | **REJECTED** (inherits IsNaiveGammaOne defect) |
| `IsGammaZero` | Basic:94 | **NEEDS-FIX** (surrogate wrong in char p ∣ N — Ker F; fix clause or caveat) |
| `sectionVanishingIdeal` | Incidence:53 | SURVIVED (non-projective junk documented) |
| `sectionVanishingIdeal_spec` | Incidence:59 | **NEEDS-FIX** (tautology; restate with Basis.coord) |
| `baseChange` | Incidence:77 | SURVIVED |
| `IsSubdivisor` | Incidence:87 | SURVIVED |
| `exists_incidenceLocusLE` | Incidence:95 | SURVIVED |
| `exists_incidenceLocusEQ` | Incidence:103 | SURVIVED |
| `exists_subgroupLocus` | Incidence:117 | SURVIVED |
| `exists_exactOrderLocus` | Incidence:128 | SURVIVED |
| `exists_fullLevelLocus` | Incidence:139 | SURVIVED |

Score: 22 SURVIVED, 4 REJECTED, 6 NEEDS-FIX. The four rejections share two root causes: (a) KM 1.2.1/1.4.4 standing hypotheses dropped during transcription (fix: one hypothesis each); (b) `IsNaiveGammaOne` missing the global killing clause (fix: one conjunct, also repairs T-E7's functor).

## QUOTE-MISSING list (verbatim source quote absent or acknowledged-pending)

1. **KM 3.1** (Drinfeld Γ(N) definition) — `IsFullLevel`; PENDING-SOURCE(KM) per D8, still open.
2. **KM 1.10.x bridge** "Σ[Pᵢ] = Z as divisors ⟺ full set of sections" — asserted as "i.e." in `IsFullLevel`'s docstring and Basic.lean's header routing (T-D4), but outside the in-hand §§1.1–1.9; no quote anywhere.
3. **KM 3.2** (Γ₁(N) definition of record) — `IsGammaOne` locator only.
4. **KM 3.4** (Γ₀(N) definition) — `IsGammaZero` (the 1.4.1 cyclic quote IS in hand; 3.4 itself is not; the geometric surrogate has no source by design — T-D10).
5. **KM 3.7** — `isFullLevel_iff_naive`'s cited locator; no quote.
6. **KM 1.6.2/1.6.3/1.6.5 statement quotes** — `exists_exactOrderLocus` / `exists_fullLevelLocus`: decomposition-km1 D-inc.4 records the proofs-read route but no verbatim statements.
7. **KM 1.3.4 statement** — `exists_incidenceLocusLE`: proof fully transcribed (D-inc.2), verbatim statement not quoted (1.3.5 and 1.3.7 are quoted; 1.3.4 is not).
8. **KM 1.2.2/1.2.5 statements** — `sectionsDivisor(_degree)`/`degree`: D3 says "quotes at ticket-cut time"; with `sectionsDivisor_degree` REJECTED for exactly a standing-hypothesis omission, pulling the KM 1.2.1 definition-of-curve quote (separated? which exact standing assumptions) should be done *before* re-stating the fixed spec.