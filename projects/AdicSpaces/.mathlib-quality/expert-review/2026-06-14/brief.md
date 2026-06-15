# Review brief — Sheafiness of the adic structure presheaf (Wedhorn Thm 8.28(b))

*Prepared 2026-06-14 for a reviewer fluent in adic spaces / non-archimedean geometry
(Huber–Wedhorn). Self-contained: no repository or formalization access required. We use
Wedhorn's conventions throughout. This is a strategic / soundness review of the **endgame**
of a Lean formalization: the sheaf-theoretic skeleton is complete and machine-checked; three
mathematical "leaves" remain, and we want to know whether our route to close them is right.*

---

## 1. Goal

Prove **Wedhorn, *Adic Spaces*, Theorem 8.28(b)**: if `A` is a **complete strongly
noetherian Tate ring** and `(A, A⁺)` is an affinoid ring, then the structure presheaf
`𝒪_X` on `X = Spa(A, A⁺)` is a **sheaf of complete topological rings**.

The two-field sheaf criterion (separation + gluing) is fully assembled and machine-verified;
the only remaining gaps are three mathematical sub-results ("leaves"). The purpose of this
review is to sanity-check the **decomposition** (is it faithful to Huber/Wedhorn's actual
proof?) and, above all, to stress-test one **obstruction** we have hit, which we suspect may
be an artifact of how we set things up rather than a genuine mathematical barrier.

---

## 2. Background and references

### 2.1 Setting and conventions

- `A` is a complete **Tate** ring: a complete Huber ring possessing a topologically
  nilpotent unit `ϖ`. `A⁺ ⊆ A°` is an open, integrally closed subring of `A` (a ring of
  integral elements); `A°` = power-bounded elements, `A°°` = topologically nilpotent
  elements. `(A, A⁺)` is the affinoid ring. **Strongly noetherian**: `A⟨X₁,…,Xₙ⟩` is
  noetherian for all `n`.
- `X = Spa(A, A⁺)` = continuous valuations `v` on `A` with `v(a) ≤ 1` for all `a ∈ A⁺`.
- **Rational subset** `R(T/s) = { v ∈ X : v(t) ≤ v(s) ≠ 0 ∀ t ∈ T }`, with `T ⊆ A` finite,
  `s ∈ A`, subject to Wedhorn's Definition 7.29 condition that `T·A` is **open** in `A`.
  (For a Tate ring and the *whole-space* rational subsets relevant below, `T` generates the
  unit ideal, `T·A = A`.)
- **Structure presheaf** `𝒪_X(R(T/s)) = A⟨T/s⟩`, the completion of the localization `A[1/s]`
  with respect to the topology in which `A₀[T/s]` is a ring of definition (`A₀` a ring of
  definition of `A`). We write `𝒪_X(D)` for a rational subset described by a *datum*
  `D = (T, s, …)`. For `D' ⊆ D` there is a **restriction map** `𝒪_X(D) → 𝒪_X(D')`.
- **Sheaf criterion (the conclusion we formalize).** For every rational covering `(Uᵢ)` of a
  rational subset `U`, the natural map `𝒪_X(U) → ∏ᵢ 𝒪_X(Uᵢ)` is a **topological embedding
  onto the equalizer** of the two maps `∏ᵢ 𝒪_X(Uᵢ) ⇉ ∏ᵢ,ⱼ 𝒪_X(Uᵢ ∩ Uⱼ)`. We split this
  into two fields:
  - **embedding** — the map is a topological embedding (injective + subspace topology);
  - **gluing** — every compatible family in `∏ᵢ 𝒪_X(Uᵢ)` is in the image (Čech `H¹ = 0`).

### 2.2 References

- **[Wedhorn]** T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1. Our primary source.
  Specifically: Thm 8.28(b); Cor 8.32; Lemma 8.34; Prop 8.30; Remark 7.55; Prop 7.51;
  Prop 6.18; Example 6.38; Lemma 8.31; Prop 6.16; Prop 6.21; Cor 7.32; Lemma 7.54;
  Prop A.3, A.4.
- **[Hu2], [Hu3]** R. Huber. [Hu3] = "A generalization of formal schemes and rigid analytic
  varieties", *Math. Z.* **217** (1994), 513–551 (Wedhorn's Lemma 7.54 is [Hu3] Lemma 2.6);
  [Hu2] = *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*, Aspects of
  Mathematics E30, Vieweg, 1996 (home of much of the sheafiness machinery).
- **[BGR]** S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren **261**,
  Springer, 1984. (Open mapping / Banach theory over non-archimedean fields.)
- **[Henkel]** *Open Mapping Theorem for rings with a zero unit sequence*, arXiv:1407.5647.
  (Consulted for a Pettis-style measurable-lift argument — see §8.4.)

### 2.3 State of the art

8.28(b) is classical (Huber). To our knowledge this is the first proof-assistant
formalization. The genuinely deep inputs — the open-mapping theorem (Prop 6.18), the
complete-affinoid Nullstellensatz (Prop 7.51), and the structure-presheaf machinery of §8.1
— are exactly the analytic facts Wedhorn imports from Huber and BGR, so they are where our
remaining work concentrates.

---

## 3. Strategy

We follow Wedhorn's proof of 8.28(b) verbatim:

1. **Reduce to two fields (Prop A.4).** Sheafiness = *embedding* + *gluing* for rational
   covers.
2. **Embedding** = *injectivity/separation* (from **Cor 8.32**: the restriction
   `A → ∏ᵢ 𝒪_X(Uᵢ)` is faithfully flat, hence injective) + *topological inducing* (the open
   mapping content, **Prop 6.18**).
3. **Faithful flatness (Cor 8.32)** rests on **Prop 8.30**: each restriction map
   `𝒪_X(D) → 𝒪_X(D')` (for `D' ⊆ D` rational) is **flat**.
4. **Prop 8.30** is proved in two reductions. (a) *"We may assume `X = V`"*: base-change to
   `B := 𝒪_X(D)` identifies `𝒪_X(D') ≅ 𝒪_{Spa B}(\mathrm{im}\,D')`, where `im D'` is a
   *whole-space* rational subset of `Spa B`, and intertwines the restriction with the
   canonical map `B → 𝒪_{Spa B}(im D')`. (b) **Remark 7.55**: a whole-space rational subset
   `R(T/s)` of `Spa B` (with `T·B = B`) is reached from `Spa B` by a finite chain of *basic
   Laurent steps* `Spa B ⊇ X₀ ⊇ X₁ ⊇ ⋯ ⊇ Xₙ = im D'`; each step is flat (a single Laurent
   localization), and one composes via transitivity of flatness.
5. **Gluing** = **Lemma 8.34** (Čech acyclicity of a rational cover generated by a finite
   `T ⊆ A` with `T·A = A`), assembled from: (i) Laurent covers are acyclic; (ii) a
   dominating-unit refinement (Cor 7.32) to a unit-generated cover; (iii)/(iv) **Prop A.3**.

The formalization mirrors this dependency tree exactly. **Every node except the three leaves
in §6 is machine-checked.**

---

## 4. Definitions the reviewer needs

**Definition 4.1 (presheaf value / `A⟨T/s⟩`).** For a rational datum `D = R(T/s)`,
`𝒪_X(D)` is the completion of `A[1/s]` in the topology making `A₀[T/s]` (the subring
generated by a ring of definition `A₀` and the elements `t/s`) a ring of definition.

**Definition 4.2 (case (a) vs case (b) — important for the obstruction).** Two regimes
recur. *Case (a)*: `A` is an integral domain **and** `A⁺` is itself a ring of definition
(`A⁺ = A₀`). *Case (b)*: the general, faithful situation — `A` need not be a domain and
`A⁺` may be a proper subring of a ring of definition. **Theorem 8.28(b) is case (b).** Many
auxiliary facts are easy in case (a) and are the crux in case (b); we have been systematically
removing case-(a) hypotheses (`A` a domain, "A⁺ is a ring of definition") from the spine.

**Definition 4.3 (loc-lift power-boundedness — "(LL)").** For a rational localization
`D' ⊆ D`, write `σ(t/s)` for the image of `t/s` in the completion `𝒪_X(D')`. We say `D` has
the *loc-lift power-bounded* property if every such `σ(t/s)` is power-bounded in `𝒪_X(D')`
(equivalently, integral over the image of `A₀[T/s]`). This is **not a Wedhorn-named
concept**; it is the hypothesis on which our construction of the restriction maps
`𝒪_X(D) → 𝒪_X(D')` and their continuity is built (it encodes the content of §8.1 / the
well-definedness of `A⟨T/s⟩`). Call it **(LL)**.

**Definition 4.4 (the base-changed whole-space datum `im E`).** Given `B := 𝒪_X(D)` and a
rational subset `E` "inside" `D`, `im E` is the whole-space rational subset `R(T̄/s̄)` of
`Spa B`, where `T̄`, `s̄` are the images in `B` of the generators of `E`, and `T̄·B = B`
(the images generate the unit ideal of `B`). This is the object of the Remark 7.55 chain.

**Definition 4.5 (basic Laurent step).** A datum `D' ⊆ E` that adds a single Laurent
generator: `D'.T = E.T ∪ {f}`, with the normalization side-conditions that `s` and all of
`T` lie in the ring of definition `A₀` and `1 ∈ T`. These are the steps `Xᵢ ⊆ Xᵢ₋₁` of the
Remark 7.55 chain.

---

## 5. Established results (machine-checked)

**Theorem 5.1 (faithful noetherianity of `A⟨T/s⟩`; Example 6.38 + Lemma 8.31).** For a
complete strongly noetherian Tate ring `A` and a rational datum `D`, the completion `𝒪_X(D)`
is again noetherian and strongly noetherian. *Sketch.* `𝒪_X(D)` is topologically of finite
type over `A`: it is a quotient of a multivariate Tate algebra `A⟨X₁,…,Xₙ⟩` by a closed
ideal (Example 6.38), via the general-`n` Tate topology (Prop 6.21) and the closedness of
every ideal of `A⟨X⟩` (Prop 6.17). t.f.t. over strongly noetherian Tate is strongly
noetherian (Remark 6.37). **No "A a domain", no "A⁺ = A₀".** ∎

**Theorem 5.2 (the "X = V" base change; the 8.16 keystone).** For `B := 𝒪_X(D)` and a
rational `E` inside `D`, there is a topological ring isomorphism `𝒪_X(E) ≅ 𝒪_{Spa B}(im E)`
intertwining the restriction `𝒪_X(D) → 𝒪_X(E)` with the canonical map `B → 𝒪_{Spa B}(im E)`.
Hence Prop 8.30 for `E ⊆ D` reduces to **whole-space flatness** `B → 𝒪_{Spa B}(im E)`.
∎ *(machine-checked; this is the entire content of reduction 4(a)).*

**Theorem 5.3 (basic-Laurent-step flatness; Prop 8.30, single step).** For a basic Laurent
step `D' ⊆ E`, the restriction `𝒪_X(E) → 𝒪_X(D')` is flat. *Sketch.* The relative
Wedhorn-2.13 locale of `D'` over `B := 𝒪_X(E)` gives an isomorphism transporting the
restriction to a canonical map `B → 𝒪_{Spa B}(\bar X)`, which is flat by the faithful
Example-6.38 + Lemma-8.31 engine; transport flatness across the iso. **The two
power-boundedness inputs it needs are exactly Wedhorn's basic-Laurent guarantees** (`1 ∈ T`
gives `1/s` power-bounded; `T ⊆ A₀` gives each `t` power-bounded). **Machine-checked,
sorry-free, no "A a domain"/"A⁺ = A₀".** ∎

**Theorem 5.4 (transitivity of flatness along a tower).** If `𝒪(E) → 𝒪(D₁)` and
`𝒪(D₁) → 𝒪(D)` are flat restriction maps, so is `𝒪(E) → 𝒪(D)` (scalar tower from presheaf
functoriality). Machine-checked. ∎

**Theorem 5.5 (σ-compact-free open mapping; Prop 6.16 core).** A continuous surjection of
complete topological groups with countably generated uniformity is open — proved **without**
the `σ`-compactness hypothesis (which is unfulfillable for the relevant `Aⁿ`), via a
units→0 dilation cover. This is the engine intended to drive Prop 6.18. Machine-checked. ∎

**Theorem 5.6 (faithfully-flat-via-maximals; Cor 8.32 criterion).** A flat ring map that is
surjective on **maximal** ideals (not merely a prime surjection) is faithfully flat; this is
the faithful form of Cor 8.32. Machine-checked. ∎

Substantial parts of the **Čech machinery for Lemma 8.34** (Laurent-cover acyclicity via the
A.3(3) induction; the dominating-unit σ-walk refinement; Lemma 7.54's ideal-generating
refinement; Prop A.3) are also built; residuals are in §8.5.

---

## 6. The three remaining leaves

| Leaf | Statement | Wedhorn locus |
|------|-----------|---------------|
| **A** (separation) | whole-space flatness `B → 𝒪_{Spa B}(im E)` for `B = 𝒪_X(D)`, `im E` a whole-space rational subset | Remark 7.55 chain |
| **B** (inducing) | the restriction `𝒪_X(U) → ∏ᵢ 𝒪_X(Uᵢ)` is a topological **embedding** (open onto its image) | Prop 6.18 |
| **C** (gluing) | Čech `H¹ = 0` for an ideal-generating rational cover | Lemma 8.34 (i)+(ii) residuals |

Leaf A is reduced (Theorem 5.2) to the **whole-space** flatness; the per-step engine
(Theorem 5.3) and the fold (Theorem 5.4) are done. **What remains for A is to build the
Remark 7.55 chain itself and fold it** — and this is where we hit the obstruction in §8.1.

---

## 7. Targets after the leaves

With A, B, C closed, the headline `IsSheafy` is immediate (the two-field assembly is already
wired and verified). There are no further targets; 8.28(b) would be complete.

---

## 8. Where we are stuck

### 8.1 The (LL) obstruction on the base-changed ring `B` — gates Leaf A *(the heart)*

To prove Leaf A we must fold the Remark 7.55 chain
`Spa B ⊇ X₀ ⊇ ⋯ ⊇ Xₙ = im E` **over `B := 𝒪_X(D)`**: each step `𝒪_{Spa B}(Xᵢ₋₁) →
𝒪_{Spa B}(Xᵢ)` is a basic Laurent step, flat by Theorem 5.3 (now read with ambient ring
`B`), and the fold is Theorem 5.4 (ambient `B`).

**The snag.** Both Theorem 5.3 and Theorem 5.4, read over an ambient ring `R`, require that
`R` have the loc-lift power-bounded property **(LL)** (Definition 4.3) — because the
restriction maps themselves are *defined* using (LL). So the chain over `B` needs **(LL) for
`B = 𝒪_X(D)`**.

But `B` is a *completion*. In our formalization (LL) is currently available only in **case
(a)**: the one general instance we have requires `B` to be an integral **domain** and `B⁺`
to be a **ring of definition** of `B`. For a completion `B = 𝒪_X(D)`:

- `B` is **not** a domain in general;
- `B⁺ = 𝒪_X⁺(D)` is **not** a ring of definition of `B` in general.

So our (LL)-instance does not apply to `B`, and the chain cannot be folded as stated. We have
verified (against the elaborated dependencies, not guessed) that (LL) is *genuinely used* by
both the per-step engine and the fold — it is not a spurious hypothesis we can simply drop.

**How (LL) enters — the precise mechanism.** The restriction map `𝒪_X(D) → 𝒪_X(D')` is built
in two steps. *First*, the **algebraic** localization map `A[1/s_D] → 𝒪_X(D')`: it exists
because `s_D` is a unit in `𝒪_X(D')` (the (LL-unit) half) and sends `t/s_D ↦ σ(t/s_D)`.
*Second*, one extends it **continuously to the completion** `𝒪_X(D) = ̂{A[1/s_D]}`. The source
carries the topology in which `A₀[T_D/s_D]` is a ring of definition; the continuous extension
exists iff this map sends `A₀[T_D/s_D]` into a **bounded** subring of `𝒪_X(D')` — iff each
generator `σ(t/s_D)` is **power-bounded**, which is exactly (LL). So **(LL) is the
boundedness/continuity condition that makes the restriction map exist at all**, not a property
of an already-given map. Consequently both the single-step flatness engine (which *produces*
the restriction map) and the transitivity fold (which *composes* them) genuinely require (LL)
on their ambient ring: there is literally no way to *state* "the chain is flat over `B`"
without (LL) for `B`. This is why the obstruction cannot be dodged by weakening a hypothesis —
the very objects (the restriction maps over `Spa B`) are undefined without it.

**Why we believe (LL) holds for `B` (so the obstruction is an artifact of our proof, not of
the mathematics).** By construction (Definition 4.5) the Laurent generators of the chain
`Xᵢ ⊆ Xᵢ₋₁` lie in a ring of definition `B₀` of `B`, hence are **power-bounded in `B`**.
Wedhorn 7.18/7.41 assert that a power-bounded element stays power-bounded under a rational
localization; so the lifts `σ(t̄/s̄)` *are* power-bounded in `𝒪_{Spa B}(Xᵢ)` — i.e. (LL) for
`B` is *true*. Equivalently and more conceptually: `(B, B⁺)` with `B⁺ = 𝒪_X⁺(D)` is again a
complete strongly noetherian Tate affinoid, so by Wedhorn's *own* recursive framework its
structure presheaf and restriction maps exist on `Spa B` — which is exactly what legitimises
the "we may assume `X = V`" reduction in the first place. **The gap is entirely on our side**:
our only *proof* of (LL) routes through the case-(a) shortcut ("`A` a domain" + "`A⁺` a ring of
definition"), which `B` fails as a completion, even though the *conclusion* (LL) holds for
`B`. A faithful (case-(b)) proof of (LL) bottoms at the complete-affinoid Nullstellensatz
(§8.2–8.3).

**This is the question we most want answered (Q1, Q2):** either a reformulation of the chain
that never needs (LL) on a completion, or the cleanest faithful proof of (LL) itself.

### 8.2 The faithful (LL) keystone — gates §8.1

(LL) has two halves for a rational localization `D' ⊆ D`:

- **(LL-unit).** `s` becomes a *unit* in `𝒪_X(D')` (so `t/s` makes sense). Our faithful route
  is via the complete-affinoid Nullstellensatz: `s` is a unit iff it has no zero on the
  rational subset, detected by Spa points (Prop 7.51/7.52).
- **(LL-bdd).** the lift `σ(t/s)` is power-bounded. Currently proved only in **case (a)**
  (`A` a domain + `A⁺ = A₀`); the faithful statement is Wedhorn 7.18 (a topology-aware
  valuative criterion: `σ(t/s)` is integral iff `v(σ(t/s)) ≤ 1` for all continuous
  valuations `v ≤ 1` on `A₀[T/s]`) combined with 7.41.

### 8.3 Soundness concern on the Nullstellensatz step (Prop 7.51) — gates §8.2

The most isolated single gap in the whole tree is **Prop 7.51 (part 2)**: *for a complete
affinoid ring `A` and a maximal ideal `𝔪 ⊆ A`, there exists `v ∈ Spa(A, A⁺)` with
`supp v = 𝔪`.* It is stated faithfully (no "A a domain"/"A⁺ = A₀").

Our intended construction (recorded in the project notes) is: `𝔪` is closed in a complete
Huber ring (Prop 7.51 part 1), so `A/𝔪` is a complete topological field; take **the trivial
valuation** `|·|_𝔪` (`= 0` on `𝔪`, `= 1` off `𝔪`) and pull back. **We are not sure this is
correct**: the trivial valuation on `A/𝔪` is continuous (hence lands in `Spa`) only if `𝔪`
is *open*, which a maximal ideal of a complete affinoid need not be. We suspect the right
object is the *canonical rank-1 valuation* on the complete non-archimedean **field** `A/𝔪`
(which exists because, by the affinoid Nullstellensatz, `A/𝔪` is a complete non-archimedean
field), not the trivial valuation. We ask the reviewer to confirm the correct construction
(Q3).

### 8.4 The Pettis-lift for the open mapping — gates Leaf B

Leaf B (topological inducing) needs **Prop 6.18** (the open-mapping/strictness statement that
upgrades "sheaf of rings" to "sheaf of *complete topological* rings"). We have the
`σ`-compact-free open-mapping engine (Theorem 5.5), but bridging it to the specific map
`𝒪_X(U) → ∏ᵢ 𝒪_X(Uᵢ)` appears to require a **Pettis-style measurable-section / lifting
argument** (à la the classical open-mapping proof) that we have not located in mathlib and
that our notes flag as "Bourbaki/Huber territory" (cf. [Henkel], arXiv:1407.5647). We are
unsure whether this is a standard result we should cite, or genuinely missing infrastructure
(Q4).

### 8.5 The Čech residuals — gates Leaf C *(a grind, lowest risk)*

Lemma 8.34 parts (i) (Laurent-cover acyclicity) and (ii) (dominating-unit σ-walk) still carry
a number of combinatorial/geometric residuals in the Čech engine. These are not gated by a
single deep keystone — they mirror the A.3 / 7.54 machinery that is mostly built — so we view
this as the most laborious but least risky of the three leaves. We are not asking specific
questions here, but flag it for completeness.

---

## 9. Questions for the reviewer

**Q1 (the obstruction — does Wedhorn's chain really need (LL) on `B`?).** In Wedhorn's actual
proof of Prop 8.30 via the Remark 7.55 chain, is flatness of the *intermediate* restriction
maps over the base-changed ring `B = 𝒪_X(D)` used, or does the argument fold the chain in a
way that only ever refers to the canonical maps `B → 𝒪_{Spa B}(Xᵢ)` and the **original**
ring `A`'s structure (so that no loc-lift/power-bounded property of the completion `B` is
required)? Concretely: is there a reformulation of the chain — e.g. transporting everything
back to covers of the *original* `X` via the isomorphisms `𝒪_{Spa B}(Xᵢ) ≅ 𝒪_X(Eᵢ)`
(Theorem 5.2 at each stage) — that sidesteps needing (LL) for a completion?

**Q2 (faithful (LL) route).** Failing a sidestep: what is the cleanest way to prove that the
localization lifts `σ(t/s)` are power-bounded in `𝒪_X(D')` for a complete strongly noetherian
Tate ring **without** assuming the ring is a domain or that `A⁺` is a ring of definition? Is
the topology-aware valuative criterion (Wedhorn 7.18) the right tool, and does it genuinely
reduce to the complete-affinoid Nullstellensatz, or is there a more direct route (e.g. via
the explicit `A⟨X⟩/I` presentation of the completion)?

**Q3 (Nullstellensatz construction).** For Prop 7.51(2) — a Spa point with support a given
maximal ideal `𝔪` of a complete affinoid ring — is the correct valuation the *canonical
rank-1 valuation on the complete non-archimedean field `A/𝔪`* (via the affinoid
Nullstellensatz that `A/𝔪` is such a field), rather than the *trivial* valuation? The trivial
valuation seems continuous only when `𝔪` is open; we want to confirm the right object before
formalizing it.

**Q4 (Pettis-lift / Prop 6.18).** The open-mapping upgrade to *complete topological* rings
seems to need a measurable-section / Pettis-style lift beyond the bare Banach open-mapping
theorem. Is this a standard, citable result for the maps in question (complete topological
groups arising as products/equalizers of affinoid algebras), and if so what is the cleanest
reference (Huber, BGR, Henkel 2014, Bourbaki TVS)? Or is it genuinely an open piece of
infrastructure?

**Q5 (overall ordering / faithfulness).** Given the above, is our planned order — close the
Nullstellensatz (Q3) → faithful (LL) (Q2) → fold the Remark 7.55 chain (Leaf A); then Leaf C
(grind) and Leaf B (Q4) — the right one? And, at the top level: is our decomposition
(embedding = faithfully-flat + open-mapping; gluing = Čech via Lemma 8.34) the decomposition
Huber/Wedhorn actually use, or is there a more economical route to 8.28(b) we are missing?

---

## 10. Document metadata

- Project: Lean/mathlib formalization of adic spaces, following Wedhorn's *Adic Spaces*
  (arXiv:1910.05934v1).
- Brief generated: 2026-06-14.
- Build status: full project compiles cleanly (recently bumped to a current mathlib); the
  headline `IsSheafy` theorem is fully assembled and reduces exactly to Leaves A, B, C.
- Self-containment: no source code, no file paths; all notation defined in §2/§4; all
  citations in §2.2 used in the body.
- Supersedes the 2026-06-09 brief (which covered only the gluing leaf / Leaf C); this brief
  covers all three leaves and centers the newly-identified (LL) obstruction.
