# Review brief — the four residual leaves of "𝒪_X is a sheaf" (Huber/Wedhorn Thm 8.28(b))

*Prepared 2026-06-19 for an expert in adic spaces / non-archimedean geometry. Self-contained:
no code access required. We are formalizing Wedhorn's* Adic Spaces *notes (arXiv:1910.05934)
in a proof assistant; this brief is purely about the mathematics of four remaining gaps.*

## 1. Goal

We have a (machine-checked) proof of **Wedhorn, Theorem 8.28(b)**: *if `A = (A, A⁺)` is a
complete strongly-noetherian Tate affinoid ring, then the structure presheaf `𝒪_X` on
`X = Spa(A, A⁺)` is a sheaf of complete topological rings.* The proof is complete and
internally consistent **except for four clearly-isolated leaves**, each traced to a specific
result in Wedhorn or Huber. We want to (a) confirm our decomposition of these four leaves is
faithful to the literature, and (b) resolve one leaf (Q1) where the only proof we can find in
the literature uses a hypothesis our setting does not have.

## 2. Setting, notation, references

### 2.1 Notation (Huber/Wedhorn conventions)

- `A` is an **f-adic (Huber) ring**: a topological ring with an open subring `A₀` (a *ring of
  definition*) carrying the `I`-adic topology for a finitely generated ideal `I ⊆ A₀`. `A` is
  **Tate** if it has a topologically nilpotent unit.
- `A°` = the subring of **power-bounded** elements; `A°°` = the ideal of **topologically
  nilpotent** elements; `A°° ⊆ A°`.
- A **ring of integral elements** `A⁺` is an open, integrally closed subring with `A⁺ ⊆ A°`
  (Wedhorn Def. 7.14); `A°` is the largest such. `(A, A⁺)` is an **affinoid ring**.
- `Cont(A)` = continuous valuations on `A`; `Cont(A)ᵃ` = the *analytic* ones (support not
  open). `Γᵥ` = value group, `ht Γᵥ` = height.
- `Spa(A, A⁺) = { v ∈ Cont(A) : v(a) ≤ 1 ∀ a ∈ A⁺ }`; `X := Spa(A,A⁺)`.
- **Rational subset** `R(T/s) = { v ∈ X : v(t) ≤ v(s) ≠ 0 ∀ t ∈ T }` (`T` finite, `T·A` open,
  `s ∈ A`). `𝒪_X(R(T/s)) = A⟨T/s⟩` = completion of `A[1/s]` with the topology whose unit basis
  is the image of `A₀[T/s]`. A **rational covering** of a rational subset `U` is a finite
  family of rational subsets covering `U`.

### 2.2 References (all in hand as PDFs except [Hu2])

- **[Wedhorn]** T. Wedhorn, *Adic Spaces*, arXiv:1910.05934 (2019).
- **[Hu1]** R. Huber, *Bewertungsspektrum und rigide Geometrie*, Regensburger Math.
  Schriften 23 (1993) — the Habilitation (≈300 pp, German). **In hand.**
- **[Hu2]** R. Huber, *Continuous valuations*, Math. Z. 212 (1993), 445–477 (largely
  subsumed by [Hu1] §2–3).
- **[Hu3]** R. Huber, *A generalization of formal schemes and rigid analytic varieties*,
  Math. Z. 217 (1994). **In hand.**
- **[BGR]** Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, Springer (1984). **In hand.**

### 2.3 State of the art

This is the standard sheaf property of adic spaces (Huber). Our task is a faithful
machine-checked proof. Wedhorn proves most of it but **explicitly defers several
functional-analytic results to [Hu1]/[BGR] with "Proof. Missing"** (see Q2). We have
formalized the combinatorial/geometric backbone (Tate-acyclicity via Lemma 7.54 + Lemma 8.34
+ Prop A.3; the Čech machinery; the faithful-flatness criterion of Cor 8.32). What remains
are the four valuation-/functional-analytic leaves below.

## 3. Strategy — where the four leaves sit

`𝒪_X` is a sheaf iff for every rational covering `(Uᵢ)` of every rational subset `U`:

- **(embedding)** `ρ : 𝒪_X(U) → ∏ᵢ 𝒪_X(Uᵢ)` is a *topological embedding* (injective +
  homeomorphism onto its subspace-topology image), and
- **(gluing)** a family `(fᵢ)` agreeing on overlaps lifts to a section over `U`.

We obtain:
- **gluing** from general-base Tate-acyclicity (7.54 + 8.34 + Prop A.3) — formalized;
- **injectivity of ρ** from Cor 8.32 (ρ is *faithfully flat*, via Prop 8.30 + a
  maximal-ideal criterion) — formalized, modulo the valuation leaves below;
- **the topological (inducing) half of embedding** from Prop 6.18 — leaf #1.

A structural constraint that shapes everything: **the completions `𝒪_X(U)` have no
noetherian ring of definition** (e.g. `ℂ_p` is complete Tate with `ℂ_p° = 𝒪_{ℂ_p}` a ring of
integral elements but no noetherian ring of definition). The formalization deliberately
avoids any "noetherian ring of definition" hypothesis on completions. This is exactly what
makes the valuation inputs delicate: we need Spa-points bounded on **all of `A°`** (so they
lie in `Spa(A,A⁺)` for the *non-ring-of-definition* `A⁺ = 𝒪_X(U)⁺`), and it is what makes
leaf #4 (Q1) potentially false-as-stated.

## 4. The four leaves

### Leaf #1 — topological inducing of the product restriction (Wedhorn Prop 6.18)

**Need.** `ρ : 𝒪_X(U) → ∏ᵢ 𝒪_X(Uᵢ)` is *inducing*: the topology on `𝒪_X(U)` is the initial
topology from the product (equivalently ρ is a homeomorphism onto its image).

**Source.** Wedhorn Prop 6.18: *for a complete noetherian Tate ring, (1) every finitely
generated module has a unique complete module topology with a countable basis at 0, and (2)
an `A`-linear map of such modules is continuous and open onto its image.* Wedhorn marks
**6.16 (Banach for Tate rings), 6.17 (noetherian ⟺ every submodule closed), and 6.18 all
"Proof. Missing"**, deferring to [Hu1] §3.5 and [BGR]. We have already formalized 6.16 in the
sharp "sequence of units → 0" form (no σ-compactness). See Q2.

### Leaf #2 — rings of integral elements are stable under completion (Wedhorn 7.47(4))

**Need.** The completion `𝒪_X(U)⁺` (built as the closure of the image of the integral closure
of the localized plus-ring) is open, integrally closed, and `⊆ 𝒪_X(U)°`.

**Source.** Wedhorn 7.47(4) = **[Hu1] 2.4.3(iv)**: under `G ↦ Ĝ` (closure) between open
subgroups of `A` and `Â`, rings of integral elements correspond. Huber's proof (in hand):
`A° ↔ Â°` by boundedness transfer; the substantive step is *"`G` integrally closed and
**open** in `A` ⟹ `Ĝ` integrally closed in `Â`"*, by a density argument using the integral
closure `H` of `G` in `A` (open since `G` is). See Q3.

### Leaf #3 — analytic Spa-point of a non-open prime, bounded on `A°` (Wedhorn 7.45 + 7.41)

**Need.** For complete affinoid `A` and a **non-open** prime `p`, there is `v ∈ Cont(A)` with
`p ⊆ supp v` and `v(a) ≤ 1` for all `a ∈ A°` (hence `v ∈ Spa(A,A⁺)` for any `A⁺ ⊆ A°`).

**Source — fully proved in Wedhorn (no Huber deferral):**
- **Prop 7.41:** `x ∈ Cont(A)ᵃ` of height 1 ⟹ `x(a) ≤ 1` for all `a ∈ A°`. (If `x(a)>1` for
  power-bounded `a`, pick `b ∈ A°°` with `x(b)≠0`; height-1 ⟹ archimedean ⟹ `x(aⁿb)>1` for
  some `n`; but `aⁿb ∈ A°°` so continuity gives `x(aⁿb)<1`, contradiction.)
- **Lemma 7.45 (general case):** retraction `r : Spv(A₀) → Spv(A₀, I)` of a dominating
  valuation `u` at a maximal ideal `m ⊇ p₀`; `r(u) ∈ Cont(A₀)` non-analytic; extends to
  analytic `v` on `A` (Lemma 7.44(3)); microbial ⟹ height-1 vertical generization `x`
  (Rem 4.12); Prop 7.41 gives `x ∈ Spa`.

We have the retraction `r` and most of the chain. Open sub-steps: 7.41, 7.44(3), and the
microbial-to-height-1 generization (Rem 4.12). We use **only** the general case (never the
"noetherian ⟹ discrete, `supp x = p`" refinement). See Q4.

### Leaf #4 — power-boundedness from Spa-boundedness (the red flag)

**Need (feeds the faithful-flatness input).** For *complete* Tate `A` with ring of integral
elements `A⁺`: if `x ∈ A` has `v(x) ≤ 1` for every `v ∈ Spa(A,A⁺)`, then `x ∈ A°`.

**Problem.** The only statement of this converse we can find is Wedhorn's remark on [Hu2]
Lemma 3.3 (density of `σ(A⁺)` in `Cont A`): *"(3) If `A` is a Tate ring **and has a
noetherian ring of definition**, the converse holds: if `A′` is integrally closed with
`σ(A′)` dense in `Cont A`, then `A′ ⊆ A°`."* The direction we need is this converse, stated
**only under "Tate + noetherian ring of definition"** — which the completions do **not**
satisfy. This is the crux of Q1.

## 5. Open questions for the reviewer

**Q1 (leaf #4 — highest priority).** Let `A` be a **complete** Tate ring with a ring of
integral elements `A⁺` but **no** noetherian ring of definition (the relevant case is a
completion `𝒪_X(U)`; `ℂ_p` is the clean toy case). Is

> `x ∈ A` and `v(x) ≤ 1` for all `v ∈ Spa(A,A⁺)`  ⟹  `x ∈ A°` (power-bounded)

true? Wedhorn gives the converse only under "Tate + noetherian ring of definition" ([Hu2]
3.3(3)). **(a)** Is there a noetherian-ring-of-definition-*free* proof — e.g. via the
analytic-point construction of Lemma 7.45 applied to an "`x` not power-bounded" witness (in
the spirit of how the *unit* criterion reduces to 7.45)? **(b)** Or is it genuinely false
without that hypothesis, and if so what is the correct faithful form of the flatness input it
stands for? (We suspect we may only need the *easy* direction `x ∈ A⁺ ⟹ v(x) ≤ 1`, or a
bound phrased on `A°` rather than `A⁺`; the minimal correct form is what we need.)

**Q2 (leaf #1).** Wedhorn defers Prop 6.18 to [Hu1] §3.5 / [BGR] ("Proof. Missing"). For the
one consequence we need — `ρ` is a topological embedding — is the faithful route through
6.18(2) (unique f.g.-module topology + open mapping), or is there a more direct
Banach-open-mapping argument ([BGR]-style: `ρ` is a continuous surjection of complete
Tate–Banach modules onto a closed image, hence open by the OMT 6.16 we already have) that
avoids the finitely-generated-module-topology uniqueness 6.18(1) entirely? Which is cleaner
and faithful?

**Q3 (leaf #2).** [Hu1] 2.4.3(iv) requires the precompletion subring `G` to be **open**. Our
`G` is the integral closure of `A⁺[T/s]` inside `A[1/s]`. **Is this integral closure open in
`A[1/s]`?** Does Wedhorn 7.19/7.20 (`(A⁺⟨X⟩_T)^int` is a ring of integral elements;
`(A°)⟨T/s⟩ ⊆ (A⟨T/s⟩)°`) already guarantee openness, or is there a gap (e.g. it is `A⁺[T/s]`
that is open, and openness of its integral closure needs a separate argument)?

**Q4 (overall faithfulness).** Does the four-leaf decomposition capture *all* the remaining
valuation-/functional-analytic content of Thm 8.28(b)? In particular: (a) is leaf #3's use of
only the *general* case of 7.45 (never the noetherian-discrete refinement) sound for the
flatness application? (b) Are we right that the *gluing* half needs none of these four leaves
(it follows purely from Tate-acyclicity 7.54 + 8.34 + Prop A.3)?

## 6. Metadata

- Subject: Wedhorn *Adic Spaces* Thm 8.28(b); four residual leaves.
- Status: full proof machine-checked and building, modulo the four isolated leaves above; the
  rest (Tate-acyclicity, Čech, Cor 8.32 faithful-flatness, the `A⁺ ⊆ A°` affinoid interface)
  is complete.
- Highest-value question: **Q1** (does the power-boundedness converse hold without a
  noetherian ring of definition).
