# SMO closure plan — 2026-05-16

*Following the 2026-05-16 expert-review reply. Replaces the analytic
Route B plan with a purely algebraic chain.*

## Goal

Discharge the three level-3 atomic sorries in
`LeanModularForms/SMOObligations.lean` so that
`HeckeRing.GL2.strongMultiplicityOne_axiom_clean` is axiom-clean
(`{propext, Classical.choice, Quot.sound}` only).

## Final-state dependency graph

```
                ┌───────────────────────────────────┐
                │  strongMultiplicityOne_axiom_clean │  ← target
                └─────────────────┬─────────────────┘
                                  │ uses (proven, no sorry)
        ┌─────────────────────────┴──────────────────────────┐
        │                                                    │
┌───────▼────────────────────────────┐    ┌─────────────────▼───────────┐
│  newform_unique_routeB              │    │  eigenvalues_eq_all_coprime  │
│  (proven, no sorry)                 │    │  _of_eq_off_finite           │
└───────┬─────────────────────────────┘    │  (algebraic bridge)          │
        │ uses                              │  (proven, no sorry)          │
┌───────▼─────────────────────────┐         └────────────┬─────────────────┘
│  mainLemma_charSpace_routeB     │                      │ uses
│  (proven, no sorry)             │                      │
└───────┬─────────────────────────┘                      │
        │ uses                                            │
┌───────▼─────────────────────────┐         ┌─────────────▼────────────┐
│  Sieve obligation (SMO-L3-S)    │ ────uses│  Recurrence obl (SMO-L3-R)│
│  squarefree IE decomposition    │ ◀───────┤  λ_{q²} = λ_q² − χ(q)q^(k-1)│
└───────┬─────────────────────────┘         └──────────────────────────┘
        │ uses
┌───────▼─────────────────────────┐
│  Projection obl (SMO-L3-P)      │
│  P_p = V_p∘U_p package          │
└──────────────────────────────────┘
```

## Three level-3 atomic sorries (in dependency order)

| ID | Lean name | What it asserts | Depends on |
|---|---|---|---|
| **SMO-L3-P** | `exists_same_level_p_supported_projection` | For each prime `p ∣ N`, a same-level linear endo `P_p` on `S_k(Γ₁(N))` with `a_n(P_p f) = a_n(f)` if `p ∣ n` else `0`, and `χ`-preservation | — |
| **SMO-L3-R** | `newform_eigenvalue_at_prime_sq` | For every newform `f` and prime `q ∤ N`, `λ_{q²}(f) = λ_q(f)² − χ(q)·q^(k−1)` | — |
| **SMO-L3-S** | `coprimeSieve_admits_squarefree_decomposition_in_charSpace` | The squarefree inclusion-exclusion sieve identity: `f = Σ_{∅≠T⊆primes(N)} (−1)^{|T|+1} ∏_{p∈T} P_p f` | SMO-L3-P |

## Suggested order

**Phase 1 (parallel)**: Close SMO-L3-R and SMO-L3-P concurrently.  Both
are independent; SMO-L3-R is the smaller one and can serve as a warm-up.

## Progress

### 2026-05-16 — SMO-L3-R DONE

`newform_eigenvalue_at_prime_sq` discharged.  Verified axiom-clean
(`{propext, Classical.choice, Quot.sound}`).  Strategy: lift the project's
operator-level `heckeT_ppow_succ_succ` recurrence at `r = 0` to the
ModularForm level using `heckeT_n_cusp_toModularForm'`, then apply the
eigenform property at `q` and `q²` plus the diamond eigenvalue from
`mem_modFormCharSpace_iff`, then cancel scalars using non-vanishing of
`F = f.toCuspForm.toModularForm'` (from `f.isNorm`).  ~95 LOC.

### 2026-05-16 — SMO-L3-P obstruction surfaced

The reviewer's proposed construction `P_p := V_p ∘ U_p` does NOT
naturally give a same-level Γ₁(N) endomorphism — `V_p` lands at level
`Γ₁(pN)`.  The project's existing same-level `pSupportedProjection`
(via `traceGamma1 ∘ pSupportedRaise`) has the **wrong q-expansion**:
the trace sum picks up contributions from non-∞-stabilising cosets,
expressing pullbacks of f at OTHER cusps.  Documented in
`Eigenforms/AtkinLehnerProjection.lean` (T124 docstring).

**Correct construction (function-level averaging).** For `p ∣ N`:
$$P_p f(\tau) := \tfrac{1}{p} \sum_{j=0}^{p-1} f(\tau + j/p).$$
Its q-expansion at ∞ is $\sum_{p \mid n} a_n q^n$ (the "p-supported
part").  Γ₁(N)-invariance: for $\gamma = \left(\begin{smallmatrix}a & b\\ cN & d\end{smallmatrix}\right) \in \Gamma_1(N)$ with $p \mid N$, the
map $j \mapsto jd \bmod p$ is a bijection on $\{0, \ldots, p-1\}$
(since $d \equiv 1 \pmod N$ is coprime to $p$), and $\gamma(\tau + j/p)
= \gamma'_j (\tau + j_0(j)/p)$ for a corresponding $\gamma'_j \in
\Gamma_1(N)$ (with $j_0(j) = jd \bmod p$).  The slash factors
$(cN \cdot \tau + d)^k$ cancel, giving $(P_p f) \mid_k \gamma = P_p f$.

**Lean construction estimate**: ~200–300 LOC.  Substantial but
mechanical given the math worked out above.  The averaging is NOT a
slash by any integer matrix, so the existing slash/Hecke infrastructure
doesn't apply directly; the operator must be built from scratch.

**Path** (5 sub-sorries; all foundation pieces stated in
`SMOObligations.lean`):
1. `upperHalfPlane_translate_im` — translation by reals stays in ℍ. **DONE** (1 LOC).
2. `pSupportedAvgFun` — operator definition. **DONE** (4 LOC).
3. `pSupportedAvgFun_slash_invariant` — Γ₁(N)-slash-invariance. **OPEN**.
4. `pSupportedAvgFun_qExpansion_coeff` — q-expansion formula. **OPEN**.
5. `pSupportedAvgFun_diamondOp_commute` — diamond commutation, χ-preservation. **OPEN**.
6. Use 3+4+5 to discharge `exists_same_level_p_supported_projection`. **OPEN**.

Sub-sorries 3, 4, 5 are the genuine math content remaining for SMO-L3-P
(plus the assembly step).  Each is independent and tractable:

- **Sub-sorry 3 (slash-invariance)**: ~80–120 LOC.  Use the bijection
  `j ↦ jd mod p` on `Finset.range p` (`d ≡ 1 mod N` coprime to `p`)
  and matrix conjugation `γ(τ+j/p) = γ'_j (τ+j_0(j)/p)` with
  `γ'_j ∈ Γ₁(N)`.  The cancellation of `(cNτ+d)^k` factors uses
  `f|_k γ'_j = f`.

- **Sub-sorry 4 (q-expansion formula)**: ~50–80 LOC.  The Fourier
  expansion `f(τ+j/p) = Σ_n a_n e^{2πi n j/p} e^{2πi n τ}` and the
  geometric-sum identity `Σ_{j=0}^{p-1} e^{2πi n j/p} = p · [p∣n]`.

- **Sub-sorry 5 (χ-preservation / diamond commute)**: ~50–80 LOC.
  The diamond action by `γ_d ∈ Γ₀(N)` permutes the shifts via the same
  bijection used in sub-sorry 3.

### 2026-05-16 — Session progress (2nd beastmode invocation)

- `fin_mul_mod_bijection` **DONE** (axiom-clean): combinatorial bijection
  `Fin p → Fin p`, `j ↦ jd mod p`, for `d` coprime to `p`.  Used
  `Nat.ModEq.cancel_right_of_coprime` from mathlib.

### 2026-05-16 — Session progress

- `SMOObligations.lean` compiles cleanly with 4 sorries.
- **DONE** axiom-clean:
  - `newform_eigenvalue_at_prime_sq` (SMO-L3-R)
  - `upperHalfPlane_translate_im` (foundation helper)
  - `pSupportedAvgFun` (operator definition)
  - `pSupportedAvgFun_diamondOp_commute` (A.L3.proj.5 — χ-preservation)
- **OPEN** sub-sorries:
  - `pSupportedAvgFun_slash_invariant` (A.L3.proj.3 — the technical heart, ~80–120 LOC)
  - `pSupportedAvgFun_qExpansion_coeff` (A.L3.proj.4 — Fourier-series arg, ~50–80 LOC)
  - `exists_same_level_p_supported_projection` (A.L3.proj assembly — packages
    pSupportedAvgFun as a CuspForm endomorphism, ~80–150 LOC, depends on
    the slash-inv + q-exp sub-sorries plus holo/cuspidal-at-cusps proofs)
  - `coprimeSieve_admits_squarefree_decomposition_in_charSpace` (SMO-L3-S,
    ~150–250 LOC, depends on SMO-L3-P)

Path forward documented above.  Each of the 4 remaining sorries is
the right granularity for a focused worker pass.

**Phase 2**: Close SMO-L3-S once SMO-L3-P is done.

---

## Phase 1 — Parallel work

### Ticket SMO-L3-R — newform eigenvalue recurrence at prime squares

**Statement.**  For every `f : Newform N k`, every Nebentypus `χ` and
every prime `q ∤ N`:
$$\lambda_{q^2}(f) = \lambda_q(f)^2 - \chi(q) \cdot q^{k-1}.$$

**File**: `LeanModularForms/SMOObligations.lean`
**Lean name**: `newform_eigenvalue_at_prime_sq`
**Estimated effort**: small, ~50 LOC.

**Approach.**

1. Use the project's operator-level recurrence `heckeT_ppow_succ_succ`
   at `r = 0`:
   $T_{q^2} = T_q \circ T_q - q^{k-1} \cdot \langle q \rangle \circ T_1$
   (where `⟨q⟩ = diamondOp` and `T_1 = id`).
2. Apply both sides to `f.toCuspForm` (or `f.toModularForm'`).
3. Use the eigenform property: `T_q f = λ_q(f) · f` and
   `⟨q⟩ f = χ(q) · f` (the latter because `f ∈ cuspFormCharSpace k χ`).
4. Conclude `λ_{q²}(f) · f = (λ_q² − χ(q) q^(k-1)) · f`.  Since `f ≠ 0`
   (it's a normalised newform with `a_1 = 1`), divide.

**Risks.**
- The project's recurrence is at the `Module.End` level; need to lift to
  the eigenvalue level for `Newform.eigenvalue`.
- The diamond action `⟨q⟩ f = χ(q) · f` requires `f` to be in
  `cuspFormCharSpace k χ`; the hypothesis is `f.toCuspForm.toModularForm' ∈
  modFormCharSpace k χ`, so we need the bridge
  `cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace`
  (axiom-clean in the project).

**Acceptance**: `lake env lean LeanModularForms/SMOObligations.lean`
clean; `lean_verify` on `newform_eigenvalue_at_prime_sq` returns
`{propext, Classical.choice, Quot.sound}` only.

---

### Ticket SMO-L3-P — same-level $p$-supported projection $P_p$

**Statement.**  For every prime `p ∣ N`, there exists a linear endo
`P_p : S_k(Γ₁(N)) → S_k(Γ₁(N))` such that:

1. ($q$-expansion formula)  For every `f` and every `n`,
   `a_n(P_p f) = a_n(f)` if `p ∣ n`, else `0`.
2. (character preservation)  For every `χ` and every
   `f ∈ S_k(Γ₁(N), χ)`, `P_p f ∈ S_k(Γ₁(N), χ)`.

**File**: `LeanModularForms/SMOObligations.lean`
**Lean name**: `exists_same_level_p_supported_projection`
**Estimated effort**: medium-large, ~250–350 LOC. Has the most
subsidiary work of the three.

**Approach.**

The classical construction is $P_p = V_p \circ U_p$:

- $U_p$ at level $\Gamma_1(N)$ is the bad-prime Hecke operator
  `heckeT_p_divN` (axiom-clean, project-supplied).  Acts on
  $q$-expansion: $a_n(U_p f) = a_{np}(f)$.
- $V_p$ at level $\Gamma_1(N) \to \Gamma_1(pN)$ is
  `modularFormLevelRaise` (axiom-clean).  Acts on $q$-expansion:
  $a_n(V_p f) = a_{n/p}(f)$ if $p \mid n$, else $0$.

Composition $V_p \circ U_p$: $a_n((V_p U_p f)) = a_n(f)$ if $p \mid n$,
else $0$.

**Subsidiary tickets.**

#### SMO-L3-P.1 — Level descent

The composition `V_p ∘ U_p` naturally outputs at level $\Gamma_1(pN)$,
not $\Gamma_1(N)$.  But for $f$ with the right structure, the image is
actually $\Gamma_1(N)$-invariant.

Two possible approaches:

- **Approach A (direct construction).**  Define $P_p$ at the level of
  functions $\mathfrak{H} \to \mathbb{C}$ via the explicit formula
  $P_p f (\tau) = \tfrac{1}{p}\sum_{j=0}^{p-1} f(\tau + j/p)$.  Verify
  $\Gamma_1(N)$-invariance directly (uses $p \mid N$).  This is the
  "averaging" form of the $p$-supported projection.
- **Approach B (via existing operators).**  Show that the image of
  `modularFormLevelRaise (heckeT_p_divN f)` is $\Gamma_1(N)$-invariant
  (not just $\Gamma_1(pN)$-invariant) when $p \mid N$, then bundle as a
  $\Gamma_1(N)$-cusp form.

Approach A is cleaner mathematically; Approach B reuses more project
infrastructure.  **Default: Approach A.**

*Estimate*: 100–150 LOC.

#### SMO-L3-P.2 — $q$-expansion formula

Prove $a_n(P_p f) = a_n(f)$ if $p \mid n$, else $0$.

Under Approach A: direct from
$\tfrac{1}{p}\sum_{j=0}^{p-1} e^{2\pi i n j / p} = [p \mid n]$.

*Estimate*: 30–50 LOC.

#### SMO-L3-P.3 — Bad-prime $U_p$/diamond commutation lemma

**Important**: the reviewer flagged that DS Prop 5.2.4(a) is stated only
for $p \nmid N$.  For $p \mid N$ we must **prove** the
commutation $U_p \circ \langle d \rangle = \langle d \rangle \circ U_p$
locally.

Approach: direct double-coset or Hecke-coset computation.  For each
$d \in (\mathbb{Z}/N)^\times$:

- $\langle d \rangle f = f|_k \gamma_d$ for some $\gamma_d \in \Gamma_0(N)$
  with lower-right entry $d$.
- $U_p f = \sum_b f|_k \beta_b$ for the standard $U_p$ coset reps
  $\beta_b = \begin{pmatrix}1 & b\\ 0 & p\end{pmatrix}$ ($0 \le b < p$),
  *no* $\beta_\infty$ piece (since $p \mid N$).
- $\langle d \rangle U_p f = \sum_b f|_k \beta_b|_k \gamma_d
                            = \sum_b f|_k (\beta_b \gamma_d)$.
- $U_p \langle d \rangle f = \sum_b f|_k \gamma_d|_k \beta_b
                            = \sum_b f|_k (\gamma_d \beta_b)$.
- Show that the multisets $\{\beta_b \gamma_d\}_b$ and
  $\{\gamma_d \beta_b\}_b$ coincide modulo right $\Gamma_1(N)$-action.

For $p \mid N$, $\gamma_d$ has lower-right entry $d$ and lower-left
$\equiv 0 \pmod N$ (so $\equiv 0 \pmod p$).  The conjugate
$\beta_b \gamma_d \beta_b^{-1}$ is in $\Gamma_0(N)$ (verifiable via
matrix arithmetic), so $\beta_b \gamma_d = (\text{conjugate}) \beta_b
\in \Gamma_0(N) \cdot \beta_b$.  Combining gives the multiset equality
modulo $\Gamma_1(N)$.

*Estimate*: 80–120 LOC.

#### SMO-L3-P.4 — Character-space preservation of $V_p$

$V_p$ commutes with all diamond operators: $\langle d \rangle (V_p f) =
V_p (\langle d \rangle f)$.  Immediate from the definition of $V_p$:
$f(p \tau)|_k \gamma_d = (f|_k \gamma_d)(p \tau)$ for $\gamma_d \in \Gamma_0(N)$
acting on $\Gamma_1(N)$.

May already be available in the project as
`modularFormLevelRaise_mem_modFormCharSpace` (per the Eigenforms/
inventory).  Confirm and cite, or prove locally if not.

*Estimate*: 20–40 LOC (mostly bookkeeping).

#### SMO-L3-P.5 — Assemble the projection

Combine SMO-L3-P.1 through SMO-L3-P.4 into the final existential
statement.  Package as a `LinearMap` (or `Module.End`) with the two
properties.

*Estimate*: 30–50 LOC.

**Risks.**

- *Risk:* Approach A's $\Gamma_1(N)$-invariance verification might be
  harder than expected (the shifts $\tau \mapsto \tau + j/p$ aren't in
  $\mathrm{SL}_2(\mathbb{Z})$, so the conjugation analysis is delicate).
  Fallback to Approach B if so.
- *Risk:* The bad-prime commutation (P.3) might require subsidiary
  matrix-arithmetic lemmas that aren't in the project.  Estimate
  +50 LOC if needed.
- *Risk:* Mathlib's `Units.ne_zero` quirk may cause hiccups in
  $\chi$-preservation.  Workaround: explicit coercion arguments.

**Acceptance**: clean compile; axiom check returns standard triple.

---

## Phase 2 — Sequential work (after SMO-L3-P)

### Ticket SMO-L3-S — squarefree inclusion-exclusion sieve

**Statement.**  For every Nebentypus $\chi$ and every
`f ∈ S_k(Γ₁(N), χ)` with $a_n(f) = 0$ for all $n$ coprime to $N$:
there exists $f_d : \mathbb{N} \to S_k(\Gamma_1(N))$ such that

- $f = \sum_{d \mid N,\; d > 1} f_d(d)$;
- $f_d(d) \in \mathrm{qSupportedOnDvdSubmodule}\;N\;k\;d$;
- $f_d(d) \in \mathrm{cuspFormCharSpace}\;k\;\chi$.

**File**: `LeanModularForms/SMOObligations.lean`
**Lean name**: `coprimeSieve_admits_squarefree_decomposition_in_charSpace`
**Estimated effort**: medium, ~150–250 LOC.
**Depends on**: SMO-L3-P.

**Approach.**

Use the existential from SMO-L3-P to obtain $P_p$ for each prime
$p \mid N$.  For each nonempty squarefree $T \subseteq \mathrm{primes}(N)$,
define
$$g_T := (-1)^{|T|+1}\, \left(\prod_{p \in T} P_p\right) f.$$

Properties to verify:

1. $g_T \in \mathrm{qSupportedOnDvdSubmodule}\;N\;k\;(\prod T)$: from
   the $q$-expansion formula iterated over $T$.
2. $g_T \in \mathrm{cuspFormCharSpace}\;k\;\chi$: each $P_p$ preserves,
   so the composite does.
3. Reconstruction: $\sum_{\varnothing \ne T} g_T = f$ when $a_n(f) = 0$
   for $\gcd(n, N) = 1$.  By coefficient-wise comparison and the
   inclusion-exclusion identity
   $\sum_{\varnothing \ne T \subseteq \mathrm{primes}(N)} (-1)^{|T|+1} \prod_{p \in T} [p \mid n]
   = [\gcd(n, N) > 1]$.
   The RHS is $1$ on the support of $f$ (since $a_n(f) = 0$ for $\gcd(n,N)=1$),
   so the alternating sum reconstructs $f$.

Finally, set $f_d := g_T$ for $d = \prod T$ squarefree, and $f_d := 0$
for non-squarefree $d > 1$.  This matches the API shape required by
`mainLemma_charSpace_of_sameLevelDivisorDecomposition`.

**Subsidiary tickets.**

#### SMO-L3-S.1 — Coefficient-wise inclusion-exclusion identity

The combinatorial identity
$$\sum_{\varnothing \ne T \subseteq \mathrm{primes}(N)} (-1)^{|T|+1} \prod_{p \in T} [p \mid n]
= [\gcd(n, N) > 1].$$

May already exist in the project (e.g., `coprime_indicator_eq_sum_moebius`
in `Eigenforms/MainLemma.lean`).  Verify the existing form and adapt
if needed.

*Estimate*: 30–50 LOC.

#### SMO-L3-S.2 — Iterated $q$-expansion under composition of $P_p$

For nonempty $T = \{p_1, \ldots, p_m\}$:
$$a_n\left(\prod_{p \in T} P_p\;f\right) = a_n(f) \quad \text{if } \prod T \mid n,\; \text{else } 0.$$

Direct from iterating SMO-L3-P's coefficient formula.

*Estimate*: 30–50 LOC.

#### SMO-L3-S.3 — Reconstruction at the $q$-expansion level

Combine S.1 and S.2: for every $n$,
$$\sum_{\varnothing \ne T} a_n(g_T) = a_n(f) \cdot [\gcd(n, N) > 1].$$

Under the hypothesis $a_n(f) = 0$ for $\gcd(n, N) = 1$, the RHS equals
$a_n(f)$ for every $n$.

*Estimate*: 40–60 LOC.

#### SMO-L3-S.4 — Lift to modular-form equality

Use the project's `qExpansion_injective` (or equivalent) to upgrade the
coefficient-wise equality to a cusp-form equality.

*Estimate*: 20–40 LOC.

#### SMO-L3-S.5 — Re-index and zero-fill to match API

The sum is over nonempty squarefree subsets $T$.  Re-index to
`d ∈ N.divisors.filter (1 < ·)` by the bijection $T \mapsto \prod T$
on squarefree divisors of $N$, zero-filling non-squarefree divisors.

*Estimate*: 30–50 LOC.

**Risks.**

- *Risk:* `qSupportedOnDvdSubmodule` is defined in the project — confirm
  the precise definition matches "$q$-supported on multiples of $d$"
  exactly.
- *Risk:* Squarefree/non-squarefree re-indexing may require fiddly
  `Finset` manipulations.  Use `Finset.image (∏ T)` over
  `Finset.powerset (primes N) \ {∅}`.

**Acceptance**: clean compile; axiom check on
`mainLemma_charSpace_routeB` returns standard triple.

---

## What is explicitly **not** in this plan

Per the 2026-05-16 reviewer feedback:

- **No Hecke functional equation formalisation.**  The previous
  `newform_heckeEntireExtension` obligation is removed from the SMO
  critical path.  May be tackled separately as long-term L-function
  infrastructure, but it is not needed for SMO.
- **No Dirichlet L-function trivial-zero contradiction.**  The previous
  `newform_noEntireExtensionUnderBadPrime` obligation is removed.  The
  algebraic finite-exception bridge (already proven, no sorry) replaces
  it entirely for SMO.  If analytic non-vanishing is needed later, the
  reviewer recommends Rankin–Selberg rather than the trivial-zero quotient.
- **No Petersson adjoint chain.**  Route A (DS Thm 5.5.3) is off the
  SMO critical path.  The two remaining sorries in
  `petN_heckeT_p_symmetric_form` are NOT part of this plan.  They may
  be discharged later for spectral applications.

---

## Acceptance criteria

When all three level-3 tickets are closed:

1. `lake env lean LeanModularForms/SMOObligations.lean` compiles
   with **zero `sorry` warnings**.
2. `lean_verify HeckeRing.GL2.strongMultiplicityOne_axiom_clean`
   returns `{propext, Classical.choice, Quot.sound}` only — no
   `sorryAx`.
3. The unconditional theorem
   `HeckeRing.GL2.strongMultiplicityOne` in `Newforms.lean` can also
   be closed by patching its body to call
   `strongMultiplicityOne_axiom_clean`, or by inlining the proof.

---

## Estimated total effort

| Ticket | LOC range | Sub-tickets |
|---|---|---|
| SMO-L3-R | 50 | 1 |
| SMO-L3-P | 250–350 | 5 (P.1–P.5) |
| SMO-L3-S | 150–250 | 5 (S.1–S.5) |
| **Total** | **450–650 LOC** | **11 sub-tickets** |

Realistic schedule:

- **Day 1**: SMO-L3-R complete (warm-up).
- **Days 2–5**: SMO-L3-P (parallel-able with SMO-L3-R if two workers).
- **Days 6–8**: SMO-L3-S.
- **Day 9**: integration + axiom check + patch `Newforms.lean`'s
  `strongMultiplicityOne`.

For a single worker: ~1.5–2 weeks.  For two parallel workers
(SMO-L3-P and SMO-L3-R independently in Phase 1): ~1 week.
