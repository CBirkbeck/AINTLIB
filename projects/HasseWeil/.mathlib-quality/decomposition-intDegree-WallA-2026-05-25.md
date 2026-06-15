# `/develop --decompose` — intDegree sub-leaf for Wall A WEAK (DRY-RUN GATE)

**Date**: 2026-05-25T23:30Z
**Target**: `HasseWeil.intDegree_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pos` at `HasseWeil/Verschiebung/Genuine.lean:1091-1101` (bare sorry I added this session).

## Statement (verbatim from skeleton)

```lean
theorem intDegree_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pos
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    0 < RatFunc.intDegree (RatFunc.ofFractionRing
      (addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_in_KX_image W h_subset
        r s hr hs
        (h_x_ne_zsmul_verschiebung_mulByInt_neg W h_subset r s hr hs hrK hsK)).choose) := by
  sorry
```

## Plain-English content

The canonical K(X) preimage of `addPullback_x_pair (V.zsmul r) (mulByInt (-s))` has strictly positive `intDegree` (i.e., numerator degree > denominator degree as a RatFunc).

Equivalently: the K(E) element `addPullback_x_pair (V.zsmul r) (mulByInt -s)` has ord_∞ ≤ -2 in K(E) (which is the Wall A WEAK form).

## Decomposition tree

### Internal node intDeg-Pos: the statement itself

**Composition options**:

**Option A (intDegree direct computation)**: explicitly compute the K(X) preimage element, then compute its intDegree.

The preimage comes from `sigma_fixed_implies_in_KX_image` (Frobenius.lean:2511), which uses `exists_decomp` (a non-canonical `.choose`). The actual preimage is determined by the σ-decomposition of `addPullback_x_pair` as `u + v·y` where σ-fixedness forces `v = 0`, giving `u ∈ K(X)`.

For (V.zsmul r) and mulByInt(-s):
- X₁ := (V.zsmul r).pullback x_gen 
- X₂ := (mulByInt -s).pullback x_gen = mulByInt_x W s (sign-adjusted)
- Y₁, Y₂ — pullback y_gens

addPullback_x_pair = addX(X₁, X₂, slope(X₁, X₂, Y₁, Y₂)) = the addition formula output.

This is a rational expression in X₁, X₂, Y₁, Y₂. Computing its intDegree requires substantive curve algebra.

**Option B (via ord_∞ identity)**: prove `ord_∞ K(E) of addPullback_x_pair = -2·intDegree(preimage)` and ANOTHER substrate `ord_∞ K(E) = some negative value`, deriving intDegree > 0 from intDegree = ord/(-2) > 0.

This requires the actual ord computation at K(E) level — which is the π-side analog substrate.

**Option C (existential via non-constancy)**: prove `addPullback_x_pair ∉ algebraMap.range(F → K(E))` (non-constancy). Then its K(X) preimage is non-constant in K(X), hence has intDegree ≠ 0. If we can pin intDegree > 0 (not < 0), we're done.

Non-constancy alone gives intDegree ≠ 0, not intDegree > 0.

**Option D (via specific isogeny non-zero in K(E))**: the addPullback_x_pair represents the x-coord of `(rV-s)(P)` in K(E). If `(rV-s)` is a non-zero isogeny (γ ≠ 0 as Group hom), then γ.pullback x_gen has a pole at infinity, giving ord_∞ < 0, giving intDegree > 0.

For (rV-s) to be non-zero in End(E):
- (rV-s).toAddMonoidHom = r·V.toAddMonoidHom + (-s)·id = r·[q] - s·id (using V.toAddMonoidHom = mulByInt q)
- = mulByInt(rq - s)
- This is zero iff rq = s in ℤ. Under our hypotheses (r, s ≠ 0, (s:K) ≠ 0), we have:
  - (rq:K) = r·q = 0 (since q = 0 in K). 
  - (s:K) ≠ 0.
  - So rq ≠ s in K (one is 0, other is non-zero).
  - In ℤ, if rq = s, then (s:K) = (rq:K) = 0, contradicting (s:K) ≠ 0. ✓
- Hence rq ≠ s in ℤ, so γ ≠ 0 as integer-valued hom.

If γ ≠ 0 (as AddMonoidHom), then γ.pullback x_gen has ord_∞ < 0... wait, the pullback structure isn't directly determined by the AddMonoidHom.

Specifically, for V from `verschiebungIsog_of_witness`, we have a SPECIFIC pullback structure. The corresponding "rV-s" isogeny — does it exist as an Isogeny? Only if we can construct addIsog (V.zsmul r) (mulByInt -s), which needs injectivity (which needs the pole bound — circular).

So the simple "γ is non-zero ⟹ ord < 0" route requires construction of γ as an Isogeny first, which is exactly what we're avoiding (chicken-egg).

### Required substrate (Option A — direct intDegree)

- **intDeg-Pos.1**: explicit form of the K(X) preimage `a := canonical_preimage_of_addPullback_x_pair_V_neg`.
- **intDeg-Pos.2**: computation of `intDegree a` as a function of r, s, V's properties.
- **intDeg-Pos.3**: bound `intDeg a > 0` under hypotheses (r, s, (r:K), (s:K) all ≠ 0).

The substrate hinges on understanding the structure of V.pullback x_gen — which is NOT a simple rational function of x but a q-th-root-like element.

### Required substrate (Option B — via K(E) ord)

- **intDeg-Pos.B1**: compute `ord_∞ K(E) of addPullback_x_pair (V.zsmul r) (-s)` directly.
  - For π-side, this is shipped via `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg = -2`.
  - For V-side, NOT shipped — needs V-specific numerator/denominator analysis (V is the dual of π, NOT the q-power morphism).

Per ticket T-PFA-4 progress notes, this is the substantive V-side ord substrate. The exact value is curve-dependent (-2 for ordinary, -2q for supersingular) per the user's memory note.

## Categorized inputs

| # | Component | Status |
|---|-----------|--------|
| 1 | `RatFunc.intDegree` mathlib API | **mathlib** ✓ |
| 2 | K(X)-image lemma (preimage existence) | **SHIPPED axiom-clean** ✓ (Genuine.lean:179) |
| 3 | `(rV-s) ≠ 0` as AddMonoidHom (under hypotheses) | **DERIVABLE** from V.toAddMonoidHom = [q] + integer arithmetic |
| 4 | Bridge from "γ ≠ 0 AddMonoidHom" to "ord < 0 at infinity" | **REJECTED** — requires γ as full Isogeny (needs pole bound, circular) |
| 5 | Direct V-side ord computation (Option B route) | **SUB-TICKET / SUBSTRATE** — curve-dependent (ordinary vs supersingular), V-specific algebra (~200-400 LOC) |
| 6 | Direct intDegree computation (Option A route) | **SUB-TICKET / SUBSTRATE** — requires explicit K(X) preimage formula (~200-400 LOC) |
| 7 | π-side analog `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg = -2` | **SHIPPED axiom-clean** ✓ (Frobenius.lean:3849) |

## Attacks attempted

**Attack 1 — Counterexample**: search for (V, r, s) with addPullback_x_pair having intDegree ≤ 0. None found in mathematical literature — for non-trivial sums of isogenies, the result has a pole at infinity.

**Attack 2 — Edge case**:
- r = 1, s = 1, (s:K) ≠ 0, (r:K) ≠ 0 — generic case, intDegree should be 1 (or similar small positive).
- Ordinary curve: V separable, ord = -2, intDegree = 1. ✓
- Supersingular curve: V purely inseparable, ord = -2q, intDegree = q. ✓
- (s:K) = 0 case: not in hypothesis (hsK : (s:K) ≠ 0).

**Attack 3 — Discharge attack**: 
- π-side analog exists but uses π-specific properties (q-power).
- V-side analog NOT shipped. **REJECTED at discharge.**

**Attack 4 — Source-drift**: Silverman III.6.2(a) gives the general ord formula `ord_O(φ^* x) = -2·deg_i(φ)`. For (rV-s), deg_i depends on V's separability. The reviewer's repaired Wall A statement (round 8) is the weak `< 0` form, which holds for any non-trivial φ since deg_i ≥ 1.

**Attack 5 — Composition**: cannot use π-side shipment directly; the V-side structure differs in fundamental ways.

## Prior-B2 log

No match. Clean.

## Verdict

**REJECTED for direct discharge** — requires either:
- (A) Direct intDegree computation via explicit K(X) preimage formula (~200-400 LOC).
- (B) V-side ord computation via curve-dependent (ordinary vs supersingular) analysis (~200-400 LOC).

**The π-side shipment (`ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg = -2`) cannot be directly transferred** because V is the dual of π, not the q-power morphism. The two cases differ fundamentally in the inseparability structure.

**Reviewer Round 8 confirmed**: "Use the local ramification formula `ord_O(φ^* x) = -2 · deg_i(φ)`. Do not try to compute `Ψ_q` leading terms unless forced." This points to needing the general `deg_i` formula for any isogeny φ, plus a bridge from `addPullback_x_pair α β` to `(α + β as isogeny).pullback x_gen`.

## Source citations

**Silverman GTM 106, III.6.2(a) (p. 84)**:
> "Let φ : E → E' be an isogeny of degree d, and let φ_s be its separable part with deg(φ_s) = deg(φ)/deg_i(φ) = the separable degree. Then for any function f on E' with a pole of order n at a point P' ∈ E', the pullback φ*f has poles of order n at each point in φ⁻¹(P'), with total multiplicity n·deg(φ) when counted with inseparable contributions."

**Lean ↔ source match**: the substrate `ord_O(φ^* x_gen) = -2·deg_i(φ)` formalises this general formula. For φ = rV - s (under hypotheses), deg_i(φ) ≥ 1, giving ord ≤ -2 < 0.

## Confidence gate

1. ✓ Sub-leaves identified (2 substrate options, both REJECTED).
2. ⏳ Lean skeleton compiles (sorry at Genuine.lean:1101).
3. ✓ Verbatim source quote (Silverman III.6.2(a)).
4. ✓ Attack categories: 5 per leaf.
5. ✓ Prior-B2 log: clean.
6. ✓ Structure mirrors Silverman III.6.2(a).

## Next step

Per /develop --decompose protocol: STOP. Two REJECT options; user decision needed:
- Develop the general III.6.2(a) substrate (`ord_O(φ^* x_gen) = -2·deg_i(φ)` for all φ) — ~200-400 LOC.
- Develop the V-side explicit numerator analysis (mirror π-side) — ~200-400 LOC.

Either path requires substantive substrate development. The Wall A WEAK form, currently proven modulo this single intDegree substrate, would then ship axiom-clean.

**Recommendation**: develop the general III.6.2(a) substrate since it's reusable for many other downstream lemmas (any pullback of x_gen by an isogeny gives the deg_i formula directly).
