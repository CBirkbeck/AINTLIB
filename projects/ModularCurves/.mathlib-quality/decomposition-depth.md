# Decomposition — the DEPTH layer closing `be_forward_core` / `be_backward_core` (Stacks 00N1)

**Targets** (`ForMathlib/BuchsbaumEisenbud.lean`, the two remaining `sorry` cores of the
Buchsbaum–Eisenbud acyclicity criterion; DO NOT change their statements):

```lean
-- be_forward_core  (L187): exact complex, 1 ≤ i < e ⟹
--   (LinearMap.idealOfMinors (rnk i) (φ (i-1))).gradeGE i ∨ … = ⊤        -- Stacks 00N1 (1)⟹(2)(b)
-- be_backward_core (L272): grade conditions, deep interior rk(i+1)≠0 ∧ rk(i+2)≠0 ⟹
--   Function.Exact (φ (i+1)) (φ i)                                       -- Stacks 00N1 (2)⟹(1)
```

**Skeleton (buildable, sorries-only):** `ForMathlib/Depth.lean` (`lake build
ModularCurves.ForMathlib.Depth` → **Build completed successfully (8614 jobs)**, 8 `sorry` + 1 real
`def`) and `ForMathlib/Acyclicity.lean` (`lake build ModularCurves.ForMathlib.Acyclicity` → **Build
completed successfully (8616 jobs)**, 3 `sorry`).  Every leaf statement elaborates.

---

## 0. Route decision — read the ACTUAL Stacks proofs of BOTH 00N1 directions, then decide

I transcribed the source proof chains of **00N1 (Prop 10.102.9)** and every sub-result. Three
corrections to the task's premises fell out, each with decisive source evidence:

### (A) The acyclicity lemma is **00N0 (Lemma 10.102.8)**, NOT 0AVQ. The task locator was wrong.

WebFetch of tag **0AVQ** returns **"Torsion free modules" (Section 31.11)** — unrelated. WebSearch
confirms: *"Lemma 10.102.8 (00N0): Acyclicity lemma — The Stacks project"*, cited **"[Lemma 1.8,
Peskine–Szpiro]"**. 00N0 is what 00N1's backward direction invokes. `be_backward_core`'s own
docstring ("acyclicity lemma 0AVQ") is therefore mis-cited; the correct tag is **00N0**.

### (B) **Auslander–Buchsbaum (090V/0AVJ) is NOT needed** — neither 00N1 direction uses it.

The task and `be_forward_core`'s docstring propose a forward proof via `pd(M_𝔭) ≤ depth R_𝔭 <
i` (Auslander–Buchsbaum). But the **actual** Stacks 00N1 `(1)⟹(2)` proof does not touch it. Verbatim
chain of the forward proof (transcribed from 00N1):

> localise at `𝔮 ∈ Ass(R)` (depth 0), complex stays exact (Lemmas **00MY**, **00MW**); the map
> `R → ⊕_{𝔮∈Ass} R_𝔮` is injective (**0311**), so `rank φᵢ = rᵢ` over `R` and `I(φᵢ)_𝔮 = R_𝔮`; the
> product `I(φₑ)⋯I(φ₁)` avoids every `𝔮 ∈ Ass(R)`, so (prime avoidance **00DS**) pick `x` in it with
> `x` a nonzerodivisor (**00LD**); by **00MZ** the complex over `R/xR` is exact, and induction on `e`
> gives `I(φᵢ)` a regular sequence of length `i`.

Cross-reference list of the forward proof: **00MY, 00MW, 0311, 00DS, 00LD, 00MZ** — no 090V/0AVJ,
no `pd`, no Auslander–Buchsbaum. So the forward core needs NO depth invariant at all; the AB route is
a heavier alternative Stacks declines. **This file contains no Auslander–Buchsbaum leaf.**

### (C) The depth invariant collapses onto the EXISTING Rees/Ext machinery — the layer is small.

The backward core (00N1 `(2)⟹(1)`) DOES need module depth, via **00N0**, whose proof (transcribed) is:

> decompose `0 → Mₑ → ⋯ → M₀` into the syzygy short exact sequences `0 → Mₑ → Mₑ₋₁ → Kₑ₋₂ → 0`,
> `0 → Kⱼ → Mⱼ → Kⱼ₋₁ → 0`, `0 → Kᵢ₊₁ → Mᵢ₊₁ → Bᵢ → 0`, `0 → Kᵢ → Mᵢ → Mᵢ₋₁`, `0 → Bᵢ → Kᵢ → H → 0`,
> and apply **Lemma 10.72.6 [00LX]** (the depth-SES inequalities) repeatedly to push `depth Mⱼ ≥ j`
> down to `depth H ≥ 1`.

So the ENTIRE nontrivial content of 00N0 is the depth-SES inequality **00LX (Lemma 10.72.6)**. And
00LX's proof (transcribed) is: *"the characterisation of depth using the Ext groups `Extⁱ(κ, N)`
[00LW]"* + *"the long exact cohomology sequence [00LU]"*. Both are **already on this branch**:

* **00LW** (`depth(M) ≥ k ⟺ Extⁱ(R/𝔪, M) = 0 ∀ i<k`) is `ForMathlib.Grade.rees_core` at `I = 𝔪` —
  `rees_core` is proved in full there **for a GENERAL finite module `M`** (not just `M = R`); its
  statement is literally `(∃ M-regular seq of length k in I) ↔ ∀ i<k, Subsingleton (Ext (R⧸I) M i)`.
* the covariant `Ext` long exact sequence `Ext.covariant_sequence_exact₁/₂/₃` is the exact tool
  `Grade.lean` already drives (see `subsingleton_ext_quotSMulTop_iff`, `comp_mk₀_smul_id_eq_zero`).

**Route decision — the MINIMAL depth API** is just:
`HasDepthGE` (predicate, generalising `Ideal.gradeGE` to modules) + its **Ext bridge** (= `rees_core`,
HAVE) + the **three 00LX SES inequalities** (NEW, but pure Ext-LES, reusing Grade's idioms) +
**depth-1⟺not-associated-prime** (NEW, small) + **depth of a free module** (NEW, small). No numeric
`ℕ∞` depth, no Auslander–Buchsbaum, no `Tor`. Everything else the two cores need is the 00N1
scaffolding (00MY/00MW/00MZ, elementary linear algebra) + the acyclicity lemma 00N0 assembled from the
above.

---

## 1. Ordered ticket tree (topological)

`HAVE` = discharged by existing AINTLIB/mathlib; `NEW` = to build. Line numbers are into the two new
skeleton files.

```
FILE ForMathlib/Depth.lean  (the depth invariant + API)
[T-DEPTH.def]   Module.HasDepthGE  (predicate; = gradeGE for modules)     REAL def   ~5    (done)
[T-DEPTH.zero]  HasDepthGE _ _ 0 ↔ Nontrivial                             NEW        ~10
[T-DEPTH.mono]  HasDepthGE monotone in k                                  NEW        ~15
[T-DEPTH.ext]   00LW  depth ≥ k ⟺ Extⁱ(R/𝔪,M)=0 ∀i<k                      NEW≈HAVE   ~20   (= rees_core|I=𝔪)
[T-DEPTH.ses1]  00LX(1) depth B ≥ min(depth A, depth C)                   NEW        ~80
[T-DEPTH.ses2]  00LX(2) depth C ≥ min(depth B, depth A−1)   ★load-bearing NEW        ~90
[T-DEPTH.ses3]  00LX(3) depth A ≥ min(depth B, depth C+1)   ★load-bearing NEW        ~90
[T-DEPTH.ass]   00LD  depth ≥ 1 ⟺ 𝔪 ∉ Ass(M)                             NEW        ~40
[T-DEPTH.free]  depth(Rⁿ) = depth(R)                                      NEW        ~40

FILE ForMathlib/Acyclicity.lean  (00N0 + 00N1 scaffolding)
[T-ACYC.00N0]   acyclicity lemma (10.102.8)                ★★★ MAKE-OR-BREAK NEW    ~300–450
[T-ACYC.00MZ]   10.102.7  exact ⟹ exact mod nonzerodivisor                NEW        ~120
[T-ACYC.00MYW]  10.102.3+6 depth-0 exact free ⟹ I(φᵢ)=⊤                   NEW        ~300–500
```

Consumed but already **HAVE** (do not rebuild):

- `ForMathlib.Grade.rees_core` (the Ext bridge; currently `private` — expose or re-call).
- `Ideal.gradeGE_localize` (`ForMathlib.Grade`) — localises the grade conditions for 00N1-backward's
  dim-induction. PROVED, axiom-clean.
- `exists_isSMulRegular_of_forall_not_le_associatedPrimes`, `biUnion_associatedPrimes_eq_compl_regular`
  (`ForMathlib.BuchsbaumEisenbud`) — the prime-avoidance nonzerodivisor for 00N1-forward. PROVED.
- `LinearMap.idealOfMinors` + McCoy (`ForMathlib.FittingIdeals`) — the minor ideals + rank↔minors.
- mathlib: `Ext.covariant_sequence_exact₁/₂/₃`, `associatedPrimes.finite/nonempty`,
  `Module.support_eq_zeroLocus`, `IsSMulRegular`, `RingTheory.Sequence.IsRegular`, `LinearMap.baseChange`.

**Dependency order.** `[T-DEPTH.def]` ⟶ `[T-DEPTH.ext]` ⟶ `{[T-DEPTH.ses1/2/3]}` ⟶ `[T-ACYC.00N0]`;
`[T-DEPTH.ass]`,`[T-DEPTH.free]` feed the 00N0→backward-core assembly; `[T-ACYC.00MZ]`,`[T-ACYC.00MYW]`
feed the forward core independently (no depth invariant).

---

## 2. Leaves — Lean statement · verbatim source + locator · map/NEW · LOC · 3 attacks + outcomes

### [T-DEPTH.def] `Module.HasDepthGE` — REAL def, ~5 LOC
```lean
def Module.HasDepthGE (R) [CommRing R] [IsLocalRing R] (M) [AddCommGroup M] [Module R M] (k : ℕ) :
    Prop := ∃ rs : List R, rs.length = k ∧ IsRegular M rs ∧ ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R
```
**Source:** depth is *"the supremum … of the lengths of `M`-regular sequences in `I`"* (**Stacks
00LI**); over local `R` the relevant `I` is `𝔪` (**Section 10.72**, tags 00LE/00LF). We take the
`≥ k` predicate slice (no `ℕ∞`), the module analogue of `Ideal.gradeGE` (= the `M = R` case).
**Map:** NEW real def on mathlib `RingTheory.Sequence.IsRegular`.
**Attacks:** (1) *children-true/parent-false?* n/a (a def). Convention check: `HasDepthGE M 0 ↔
Nontrivial M` (empty seq regular ⟺ `M ≠ 0`) matches Stacks' "nonzero finite module" hypotheses; the
`0`-module is (correctly) never `depth ≥ 1`. (2) *source?* 00LI/00LE verbatim ("regular sequences in
`I`"); the `𝔪` specialisation is the standard local-depth. (3) *typechecks?* builds. **Outcome: sound,
leanest faithful shape; unifies with the existing `gradeGE`.**

### [T-DEPTH.ext] 00LW depth⟺Ext — NEW≈HAVE, ~20 LOC
```lean
theorem hasDepthGE_iff_forall_subsingleton_ext [IsNoetherianRing R] [Module.Finite R M] [Nontrivial M]
    (k) : HasDepthGE R M k ↔ ∀ i : Fin k, Subsingleton (Ext (ModuleCat.of R (R⧸𝔪)) (ModuleCat.of R M) i)
```
**Source (verbatim):** *"Let `R` be a Noetherian local ring with maximal ideal `𝔪`. Let `M` be a
nonzero finite `R`-module. Then `depth(M)` is equal to the smallest integer `i` such that
`Extⁱ_R(R/𝔪, M)` is nonzero."* **Stacks 00LW = Lemma 10.72.5.**
**Map:** = `ForMathlib.Grade.rees_core` at `I = 𝔪`. `rees_core` is proved there in full **for general
`M`** by the classical Rees induction (base = `IsSMulRegular.subsingleton_linearMap_iff`, step =
covariant Ext-LES dimension shift). Discharge = expose `rees_core` (drop `private`) or re-call it.
**Attacks:** (1) *parent false?* No — `rees_core`'s statement is `(∃ M-reg seq length k in I) ↔ ∀ i<k
Subsingleton (Ext (R⧸I) M i)`; at `I=𝔪` the LHS is `HasDepthGE M k` verbatim. The ONLY risk is
`rees_core` being `M = R`-only — REFUTED by reading it: it quantifies `∀ (M : ModuleCat R), Finite →
Nontrivial → …`. (2) *source?* 00LW verbatim; `≥ k` form is the immediate reformulation of "smallest
`i` with `Extⁱ ≠ 0`". (3) *typechecks?* builds (mirrors Grade's `Ext (ModuleCat.of R (R⧸I)) M i`).
**Outcome: essentially HAVE; the depth⟺Ext heart is already proved on this branch.**

### [T-DEPTH.ses1/2/3] 00LX depth-SES inequalities — NEW, ~80/90/90 LOC — (2),(3) LOAD-BEARING
```lean
-- 0 → A →f→ B →g→ C → 0 exact (hf inj, hfg exact, hg surj), finite nonzero modules
ses1 : HasDepthGE R A k → HasDepthGE R C k → HasDepthGE R B k                 -- depth B ≥ min(A,C)
ses2 : HasDepthGE R B k → HasDepthGE R A (k+1) → HasDepthGE R C k             -- depth C ≥ min(B,A−1)
ses3 : HasDepthGE R B (k+1) → HasDepthGE R C k → HasDepthGE R A (k+1)         -- depth A ≥ min(B,C+1)
```
**Source (verbatim):** for `0 → N' → N → N'' → 0` of nonzero finite modules over a local Noetherian
ring, *"(1) `depth(N) ≥ min{depth(N'), depth(N'')}`, (2) `depth(N'') ≥ min{depth(N), depth(N')−1}`,
(3) `depth(N') ≥ min{depth(N), depth(N'')+1}`"*, proved via *"the characterisation of depth using the
Ext groups `Extⁱ(κ, N)`"* [00LW] and *"the long exact cohomology sequence"* [00LU=10.71.6]. **Stacks
00LX = Lemma 10.72.6.**
**Map:** NEW, from `[T-DEPTH.ext]` + `Ext.covariant_sequence_exact₁/₂/₃` (the machinery Grade.lean
already uses). `min(x,y) ≥ k ⟺ x≥k ∧ y≥k` gives the clean predicate forms above (no `ℕ∞` truncation).
**Attacks:** (1) *children-true/parent-false?* The predicate reformulation of each `min`-inequality is
exact: e.g. (2) `min(depth B, depth A−1) ≥ k ⟺ depth B ≥ k ∧ depth A ≥ k+1`. Danger of an off-by-one
in the `−1`/`+1` — pinned by re-deriving from the Ext-LES `⋯→Extⁱ(κ,A)→Extⁱ(κ,B)→Extⁱ(κ,C)→Extⁱ⁺¹(κ,A)
→⋯` and the smallest-nonvanishing-`i` reading. (2) *source?* 00LX verbatim, all three. (3) *typechecks?*
builds. **Outcome: sound; (2),(3) are the sole engine of the acyclicity lemma (see §3), (1) kept for
completeness. Tractable — same Ext-LES pattern as the proven `subsingleton_ext_quotSMulTop_iff`.**

### [T-DEPTH.ass] 00LD depth-1 ⟺ not associated — NEW, ~40 LOC
```lean
theorem hasDepthGE_one_iff_notMem_associatedPrimes [IsNoetherianRing R] [Module.Finite R M]
    [Nontrivial M] : HasDepthGE R M 1 ↔ IsLocalRing.maximalIdeal R ∉ associatedPrimes R M
```
**Source:** 00LW base case (transcribed): *"`δ(M)=0` iff `i(M)=0`, equivalently `𝔪 ∈ Ass(M)`"* (via
**00LD**, nonzerodivisor ⟺ avoids the associated primes). **Stacks 00LD / 00LW base.**
**Map:** NEW; from `biUnion_associatedPrimes_eq_compl_regular` +
`exists_isSMulRegular_of_forall_not_le_associatedPrimes` (both HAVE, in `BuchsbaumEisenbud.lean`) with
`k = 1` (a length-1 regular sequence = one nonzerodivisor in `𝔪`).
**Attacks:** (1) *parent false?* The `[Nontrivial M]` guard is essential (else `𝔪 ∈ Ass` is empty
vacuity); kept. This is exactly "homology `H≠0` supported at `𝔪` ⟹ `¬ depth ≥ 1`", the contradiction
00N1-backward needs. (2) *source?* 00LD verbatim. (3) *typechecks?* builds. **Outcome: sound; reuses
the branch's associated-prime recipe.**

### [T-DEPTH.free] depth of a free module — NEW, ~40 LOC
```lean
theorem hasDepthGE_pi_of_hasDepthGE {n} (hn : 0 < n) (k) (h : HasDepthGE R R k) :
    HasDepthGE R (Fin n → R) k
```
**Source:** standard (`depth Rⁿ = depth R`); implicit in 00N1-backward's `depth(R^{nᵢ}) = depth(R) ≥
e`. **Map:** NEW; an `R`-regular sequence acts diagonally on `Rⁿ`, so it is `Rⁿ`-regular.
**Attacks:** (1) *parent false?* `hn : 0 < n` guard essential (`Fin 0 → R = 0` has no depth-≥-1);
present. (2) *source?* the depth-of-free identity is textbook; used implicitly in 00N1. (3)
*typechecks?* builds. **Outcome: sound, small; lets 00N0 (abstract modules) apply to the BE free
complex.**

### [T-ACYC.00N0] acyclicity lemma — NEW, ~300–450 LOC — ★★★ MAKE-OR-BREAK
```lean
theorem acyclicityLemma_hasDepthGE_homology (M : ℕ → Type u) [finite modules]
    (φ : (i) → M (i+1) →ₗ[R] M i) (hcomplex) (e) (hbdd : ∀ j, e<j → Subsingleton (M j))
    (hdepth : ∀ j, j ≤ e → HasDepthGE R (M j) j) (i) (hie : i+1 ≤ e)
    (habove : ∀ j, i<j → Function.Exact (φ (j+1)) (φ j)) :
    Function.Exact (φ (i+1)) (φ i) ∨
      HasDepthGE R (ker (φ i) ⧸ (range (φ (i+1))).comap (ker (φ i)).subtype) 1
```
**Source (verbatim):** *"Let `R` be a local Noetherian ring. Let `0 → Mₑ → Mₑ₋₁ → … → M₀` be a
complex of finite `R`-modules. Assume `depth(Mᵢ) ≥ i`. Let `i` be the largest index such that the
complex is not exact at `Mᵢ`. If `i > 0` then `H = ker(Mᵢ→Mᵢ₋₁)/im(Mᵢ₊₁→Mᵢ)` satisfies `depth(H) ≥
1`."* **Stacks 00N0 = Lemma 10.102.8** [Lemma 1.8, Peskine–Szpiro].
**Map:** NEW; the disjunctive/spot-`(i+1)` phrasing avoids `ℕ`-subtraction in the homology (both
`ker(φ i)` and `range(φ (i+1))` are submodules of `M (i+1)`) and is the contrapositive form
`be_backward_core` consumes. Proof = syzygy decomposition + repeated `[T-DEPTH.ses2]` (and
`[T-DEPTH.ses3]` once for `depth Kᵢ ≥ 1`):
```
0→Mₑ→Mₑ₋₁→Kₑ₋₂→0        ses2 ⟹ depth Kₑ₋₂ ≥ e−1
0→Kⱼ→Mⱼ→Kⱼ₋₁→0          ses2 ⟹ depth Kⱼ₋₁ ≥ j            (descend)
0→Kᵢ₊₁→Mᵢ₊₁→Bᵢ→0        ses2 ⟹ depth Bᵢ ≥ i+1
0→Kᵢ→Mᵢ→Bᵢ₋₁(⊆Mᵢ₋₁)     ses3(k=0) ⟹ depth Kᵢ ≥ 1
0→Bᵢ→Kᵢ→H→0             ses2(k=1) ⟹ depth H ≥ 1   (depth Bᵢ ≥ i+1 ≥ 2)
```
**Attacks:** (1) *children-true/parent-false?* The disjunction is faithful: assuming `habove`
(exact strictly above `i+1`), spot `i+1` is `≥` the largest non-exact index; if it IS the largest,
`depth H ≥ 1` (right); else exact (left). A one-sided claim "always `depth H ≥ 1`" would be FALSE when
`H = 0` — the disjunction correctly guards it. The syzygy modules `Kⱼ, Bᵢ` must be nonzero for the
Stacks 00LX hypotheses — genuine (they sit in the non-exact range); this is the one place the proof
must track `Nontrivial`, handled by the "largest non-exact" bookkeeping. (2) *source?* 00N0 verbatim;
the 5 SES rows are the source's own decomposition. (3) *typechecks?* builds (submodule-quotient
homology, no `i−1`). **Outcome: STATEMENT sound & faithful. PROOF rests ENTIRELY on `[T-DEPTH.ses2/3]`
= Ext-LES, which THIS BRANCH's Grade.lean already drives — the make-or-break is TRACTABLE, not a
research wall (contrast the prior doc's "multi-week" verdict, which pre-dated the `rees_core` win).**

### [T-ACYC.00MZ] exact mod nonzerodivisor — NEW, ~120 LOC
```lean
theorem exact_baseChange_quotient_of_isSMulRegular (φ) (hcomplex) (hexact) (x) (hx : IsSMulRegular R x) :
    ∀ i, Function.Exact ((φ (i+1)).baseChange (R⧸(x))) ((φ i).baseChange (R⧸(x)))
```
**Source (verbatim):** *"Suppose that `0 → R^{nₑ} → … → R^{n₀}` is exact at `R^{nₑ}, …, R^{n₁}`. Let
`x ∈ 𝔪` be a nonzerodivisor. The complex `0 → (R/xR)^{nₑ} → … → (R/xR)^{n₁}` is exact at `(R/xR)^{nₑ},
…, (R/xR)^{n₂}`."* Proof: *"the short exact sequence of complexes `0 → F_• →ˣ F_• → F_•/xF_• → 0`"* +
snake lemma. **Stacks 00MZ = Lemma 10.102.7.**
**Map:** NEW; `LinearMap.baseChange (R⧸(x))` + mathlib snake/`HomologicalComplex` LES. `[Algebra R
(R⧸(x))]` resolves (comm ring ⟹ two-sided ideal).
**Attacks:** (1) *parent false?* The base-change spelling `(φ i).baseChange (R⧸(x))` is the honest
`⊗ R/xR` of the differential; `hx : IsSMulRegular R x` is Stacks' "nonzerodivisor". (2) *source?*
00MZ verbatim. (3) *typechecks?* builds. **Outcome: sound; elementary homological algebra, forward
core only.**

### [T-ACYC.00MYW] depth-0 exact free ⟹ I(φᵢ)=⊤ — NEW, ~300–500 LOC
```lean
theorem idealOfMinors_eq_top_of_exact_of_isAssociatedPrime
    (hdepth0 : IsLocalRing.maximalIdeal R ∈ associatedPrimes R R) (e) (rk rnk) (hrk hrnk_top hrnk)
    (φ) (hcomplex) (hexact) (i) (hi1 : 1 ≤ i) (hie : i < e) :
    LinearMap.idealOfMinors (rnk i) (φ (i-1)) = ⊤
```
**Source (verbatim):** 00MY — *"Assume `𝔪 ∈ Ass(R)`, in other words `R` has depth `0`. Suppose that
`0 → R^{nₑ} → … → R^{n₀}` is exact at `R^{nₑ}, …, R^{n₁}`. Then the complex is isomorphic to a direct
sum of trivial complexes."* 00MW — for a direct sum of trivial complexes, *"the maps `φᵢ` have rank
`rᵢ`"*, *"`rank(φᵢ₊₁) + rank(φᵢ) = nᵢ`"*, *"each `I(φᵢ) = R`."* **Stacks 00MY = Lemma 10.102.3, 00MW =
Lemma 10.102.6.**
**Map:** NEW; composition 00MY (split) → 00MW (`I(φᵢ) = R`). This is the fact 00N1-forward localises
to at each `𝔮 ∈ Ass(R)`, yielding `I(φᵢ) ⊄ 𝔮`.
**Attacks:** (1) *children-true/parent-false?* Combining 00MY+00MW into one `= ⊤` conclusion needs the
given `rnk i` to be the actual rank at the split — provided by `hrnk` (the numeric rank relation, which
IS 00MW(2)); a mismatch would leave the wrong minor size. Flagged as the rank-bookkeeping detail; the
split's descending induction (00MY proof) recovers it. (2) *source?* 00MY+00MW verbatim. (3)
*typechecks?* builds (`φ (i-1)` single map, no index clash). **Outcome: sound; the fiddliest FORWARD
leaf (socle element `𝔪x=0` + matrix splitting + descending induction), but classical and bounded —
NOT a research wall.**

---

## 3. Make-or-break & attempt order

**Make-or-break: [T-ACYC.00N0] (Stacks 00N0 acyclicity lemma)** — everything the backward core needs
funnels through it, and it in turn reduces (§0(C)) to `[T-DEPTH.ses2]`/`[T-DEPTH.ses3]`.

**Attempt first, in this order (de-risking):**
1. **[T-DEPTH.ext]** — expose `rees_core`; near-instant, confirms the depth⟺Ext bridge is HAVE.
2. **[T-DEPTH.ses2]** — the single load-bearing SES inequality; if the Ext-LES bookkeeping lands here
   (it mirrors `subsingleton_ext_quotSMulTop_iff`, already proved), the make-or-break is de-risked.
   Then **[T-DEPTH.ses3]**.
3. **[T-ACYC.00N0]** — the syzygy assembly on 1–2. This is the decision point.

Parallel, independent of the depth chain (forward core): **[T-ACYC.00MZ]**, **[T-ACYC.00MYW]** — plus
the HAVE recipe `exists_isSMulRegular_of_forall_not_le_associatedPrimes`. Landing these closes
`be_forward_core` with NO depth invariant.

---

## 4. Feasibility verdict

**The depth layer is TRACTABLE given this branch's foundations — Peskine–Szpiro is NOT a deeper wall.**
Precise reasons:

- The make-or-break **00N0** has exactly one nontrivial ingredient, the depth-SES inequality **00LX**,
  and 00LX is a direct corollary of the depth⟺Ext theorem (**= `rees_core`, PROVED for general `M`**)
  plus the covariant Ext long exact sequence (**the exact machinery `Grade.lean` already drives**).
  The prior doc's "multi-week research obstruction" verdict pre-dated the `rees_core`/`ReesLocal`
  build; with it, 00N0 is syzygy bookkeeping over a proven inequality.
- The backward-core assembly around 00N0 (dim-induction, localise lower primes to exactness) reuses
  the PROVED `Ideal.gradeGE_localize`; the depth-0 contradiction reuses the PROVED associated-prime
  recipe.
- The forward core needs **no depth invariant and no Auslander–Buchsbaum** (§0(B)); its leaves
  (00MY/00MW/00MZ) are elementary linear algebra + a snake lemma, and the nonzerodivisor is HAVE.

**The two genuinely-new, bounded-but-real efforts** are (i) the syzygy bookkeeping inside **00N0**
(tracking `Nontrivial` of the syzygies `Kⱼ, Bᵢ` across the "largest non-exact spot" induction), and
(ii) the depth-0 **splitting** in **00MYW** (socle element + matrix descending induction). Both are
classical, self-contained, and free of any mathlib gap — no `Tor`, no `depth`/AB primitives beyond
what is built here. Combined NEW LOC for the whole depth layer: **~1100–1600**, versus the prior
all-of-00N1 estimate of ~800–1500 for the acyclicity monolith alone.

**Named residual risks (not walls):** (a) `[T-ACYC.00N0]`'s `Nontrivial`-of-syzygies bookkeeping is
the subtlest logic; (b) `[T-ACYC.00MYW]` splitting is the longest single proof; (c) `[T-ACYC.00MZ]`
requires wiring the raw `Fin`-free complex into mathlib's snake/`HomologicalComplex` LES. None
requires new theory absent from mathlib + this branch.

---

## 5. Files

- Depth API skeleton (buildable, 8 `sorry` + 1 real `def`):
  `projects/ModularCurves/ModularCurves/ForMathlib/Depth.lean`
- Acyclicity + 00N1 scaffolding skeleton (buildable, 3 `sorry`):
  `projects/ModularCurves/ModularCurves/ForMathlib/Acyclicity.lean`
- This decomposition: `projects/ModularCurves/.mathlib-quality/decomposition-depth.md`
- Consumers (unchanged): `ForMathlib/BuchsbaumEisenbud.lean` (`be_forward_core` L187, `be_backward_core`
  L272).

## Source locators (read against stacks.math.columbia.edu, July 2026)

00N1 (10.102.9) Buchsbaum–Eisenbud, both directions · **00N0 (10.102.8) acyclicity lemma [Peskine–
Szpiro], NOT 0AVQ** · 00LX (10.72.6) depth-SES inequalities · 00LW (10.72.5) depth⟺Ext · 00LU
(10.71.6) Ext-LES · 00LI/00LE/00LF (Section 10.72) depth def · 00LD (10.63.9) nonzerodivisor⟺Ass ·
00MY (10.102.3) depth-0 split · 00MW (10.102.6) rank+minors of a split complex · 00MZ (10.102.7) exact
mod nonzerodivisor · 00DS (10.15.2) prime avoidance · 0311 (10.63.19) `R ↪ ⊕ R_𝔮` ·
090V/0AVJ Auslander–Buchsbaum **[NOT needed — neither 00N1 direction uses it]**.
```
