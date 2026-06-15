# Review brief — Tate acyclicity (round 21)

*Prepared 2026-05-16 for ChatGPT Pro (continuing rounds 17–20).*
*Self-contained: no repo access required.*

## 1. Goal of this brief

We are implementing the round-20 reviewer-mandated domination lemma for P3
(the Wedhorn 2.13 reverse without an A-side inverse hypothesis). The
mathematical plan is in hand and matches the reviewer's prescription. The
blocker is **infrastructural**: the project's only available compactness
theorem for rational opens in $\mathrm{Spa}(A, A^+)$ takes seven explicit
witnesses, one of which (mul-archimedean valuations) is not derivable from
the standing typeclass bundle. The user has imposed a rule that disallows
adding hypotheses for convenience; this is in tension with the existing
project pattern.

This round asks a tight, focused question: **what is the right way to
discharge the compactness assumption for the domination lemma, given the
project's existing compactness API and the user's hypothesis rule?**

## 2. Background and references

### 2.1. Setting

Throughout, $A$ is a Tate ring (a complete Huber ring containing a
topologically nilpotent unit). $A^+$ is a fixed open integrally closed
subring of the power-bounded elements $A^\circ$. The adic spectrum
$\mathrm{Spa}(A, A^+)$ consists of continuous valuations $v$ on $A$
satisfying $v(a) \leq 1$ for all $a \in A^+$.

A **pair of definition** $P = (A_0, I)$ for $A$ consists of an open subring
$A_0 \subseteq A^\circ$ and a finitely generated open ideal $I \subseteq A_0$
whose powers $I^n$ form a fundamental system of neighbourhoods of $0$ in
$A_0$ (and hence in $A$, since $A_0$ is open).

A **rational open** is a subset
$R(T, s) = \{v \in \mathrm{Spa}(A, A^+) : v(t) \leq v(s) \,\forall t \in T,\ v(s) \neq 0\}$
for $T \subseteq A$ finite, $s \in A$. A **rational locality datum** $L$ packages
a pair of definition $L.P$ together with $L.T, L.s$.

### 2.2. References

- [Wedhorn 2019] Torsten Wedhorn. *Adic Spaces*. Lecture notes, 2019.
  arXiv:1910.05934. (Definitions 6.1–6.4 for pairs of definition; 7.29
  for rational subsets; Theorem 7.31 for compactness of $\mathrm{Spa}$;
  Theorem 8.28 for Tate acyclicity.)
- [Huber 1993] Roland Huber. "Continuous valuations." *Math. Z.* 212
  (1993), 455–477.
- Round-20 reviewer reply (ChatGPT Pro), dated 2026-05-16, prescribing the
  domination-lemma approach for P3.

### 2.3. State of the art

Wedhorn's Theorem 7.31 proves $\mathrm{Spa}(A, A^+)$ is quasi-compact for
Tate rings $A$. The proof goes via an embedding into a closed subset of
$\prod_{r \in A \times A} \{0, 1\}$ (the spectral / constructible topology).
The mul-archimedean restriction on valuation value groups is not visible in
Wedhorn's text — he treats all continuous valuations uniformly. The project's
formalisation of 7.31 currently routes through a closed-image criterion that
requires mul-archimedean value groups for every $v \in \mathrm{Spv}(A)$; this
is the source of the present blocker.

## 3. Strategy (recap from rounds 18–20)

The overall plan for Tate acyclicity:

1. **W1 (ticket `P7`).** Standard cover $S$ refining the given $C$ (via adic
   Nullstellensatz / Zavyalov §2.3).
2. **W2 (`P6`).** First-stage Laurent tree with dominating unit (Cor 7.32) and
   per-leaf $I_{\mathrm{units}}$ selection.
3. **W3 (`P5`).** Per-leaf relative ratio-Laurent tree refining the relative
   unit-generated cover.
4. **W3-transport (`P4`).** Lift the relative tree to an absolute
   ratio-Laurent tree via per-node application of P3.
5. **`P3`.** Per-node ratio split: given $g, h \in A$ whose canonical images in
   $\mathcal{O}(L)$ are units, produce a `RatioNodeData` packaging plus/minus
   absolute rational sub-localities with rational-open equal to
   $R(L) \cap \{v(g) \leq v(h)\}$ and $R(L) \cap \{v(h) \leq v(g)\}$.

Round-20 prescribed for P3: build the plus datum with denominator
$s^+ = L.s \cdot h$, numerator set
$T^+ = \{t \cdot h : t \in L.T\} \cup \{L.s \cdot g\} \cup B_N$, where $B_N$
is a finite generating set of $L.P.I^N$ (for $N$ chosen below). The added
$B_N$ generators make the `hopen` proof trivial and the rational-open
equality automatic.

The **substantive sub-lemma** is the **domination lemma**: for $a \in A$
nonzero on the half-space $K^+ = R(L) \cap \{v(g) \leq v(h)\}$, there exist
$N$ and a finite generating set $B_N$ of $L.P.I^N$ with $v(b) \leq v(a)$ for
all $v \in K^+$ and $b \in B_N$. The round-20 reviewer's proof outline:

> The half-space is quasi-compact (closed in the compact rational open
> $R(L)$ for Tate $A$); $a$ nonzero on it gives a uniform lower bound
> $\gamma$ on $v(a)$; $I$-adic decay of continuous valuations gives
> $v(I^N) \to 0$ uniformly for $N$ large; hence $v(b) \leq \gamma \leq v(a)$
> for $b \in I^N$.

The outline is mathematically correct and matches Wedhorn's standard
rational-subdomain technique.

## 4. The infrastructural blocker

### 4.1. Project's compactness API

The project has exactly one compactness theorem for rational opens of
$\mathrm{Spa}(A, A^+)$ in the Tate setting. It is **conditional on five
explicit witnesses plus two side conditions**:

> **Project Theorem (rational-open compactness, Tate).** *Let $A$ be a
> topological commutative ring with $\mathrm{IsHuberRing}\,A$. Suppose:*
>
> *(i) $P = (A_0, I)$ is a pair of definition for $A$ (explicit witness);*
>
> *(ii) $A_0 \subseteq A^+$ (the integrality-of-$A_0$-in-$A^+$ side condition);*
>
> *(iii) $\pi \in A_0$ with $I = (\pi)$ (principal ideal of definition);*
>
> *(iv) the image of $\pi$ in $A$ is topologically nilpotent;*
>
> *(v) the image of $\pi$ in $A$ is a unit (so $\pi$ is a pseudo-uniformizer);*
>
> *(vi) for every $v \in \mathrm{Spv}(A)$, the value group of $v$ is
> multiplicatively archimedean (call this hypothesis $\mathrm{hArch}$).*
>
> *Then for every finite $T \subseteq A$ and every $s \in A$, the preimage
> of $R(T, s)$ in $\mathrm{Spa}(A, A^+)$ is compact.*

This is the **only** rational-open compactness theorem in the project, used
throughout the Tate-acyclicity machinery (Cor 7.32, the standard-cover
extraction, the C1-assembly pipeline). Existing consumers pass the seven
items as explicit arguments propagated from the topmost call site.

### 4.2. What the domination lemma needs

For the half-space $K^+ = R(L) \cap \{v(g) \leq v(h)\}$ in
$\mathrm{Spa}(A, A^+)$: under the hypothesis that $a$ is nonzero on $K^+$
(so $v(h) \neq 0$ on $K^+$), the half-space equals the rational open
$R(T', s')$ where
$T' = \{t \cdot h : t \in L.T\} \cup \{g \cdot L.s\}$ and $s' = L.s \cdot h$.
So compactness of $K^+$ follows from the project compactness theorem applied
to this rewriting — once we have all seven witnesses.

### 4.3. What the project already gives us internally

The project lemma "Tate pair contains a top.-nilp. unit in $A_0$" extracts
a topologically nilpotent unit $\pi \in L.P.A_0$ from
$\mathrm{IsTateRing}\,A$ alone. Applying the project's
"refine the ideal of definition to a principal one, keeping the same $A_0$"
operation to a sufficiently large power of $\pi$ gives a principal pair
$P' = (L.P.A_0, \langle \pi^N \rangle)$ with
- $P'.A_0 = L.P.A_0$ (so any $L.P.A_0 \subseteq A^+$ containment propagates),
- $P'.I = (\pi^N)$ principal,
- $\pi^N$ a topologically nilpotent unit.

So items (i), (iii), (iv), (v) are **internally derivable** from
$\mathrm{IsTateRing}\,A$ plus the standing call-site hypothesis
$L.P.A_0 \subseteq A^+$ (item (ii) — already required by the caller P3
of the domination lemma, since P3 itself uses bounded-localisation arguments
that need it).

The **only item that is not internally derivable** is item (vi) — the
mul-archimedean hypothesis $\mathrm{hArch}$.

### 4.4. The user's hypothesis rule

The user has imposed a binding rule:

> *You are not allowed to skip work by adding a hypothesis; you can only
> add a hypothesis if the result is false without it.*

For $\mathrm{hArch}$: the *result* of the domination lemma (and hence Tate
acyclicity) is mathematically true for *any* Tate ring, without restriction
to mul-archimedean valuations. The proof routes through the project's Spa
compactness theorem, which uses $\mathrm{hArch}$ for technical reasons
(closed-image description via a $\{0,1\}^{A\times A}$ embedding). So
strictly, the user's rule forbids adding $\mathrm{hArch}$ — the result is
true without it; only this particular proof route needs it.

The project's existing pattern is to propagate $\mathrm{hArch}$ as a
hypothesis through every relevant theorem (Cor 7.32, the C1-assembly,
etc.). That pattern predates the user's rule.

### 4.5. Summary of the situation

| Item | Status |
|---|---|
| Pair of definition $P$ | Internally derivable |
| $A_0 \subseteq A^+$ | Available at caller (P3) |
| Principal generator $\pi$ | Internally derivable |
| $\pi$ topologically nilpotent | Internally derivable |
| $\pi$ a unit in $A$ | Internally derivable |
| **Mul-archimedean $\mathrm{hArch}$** | **Not derivable, blocks proof** |

So the *only* obstacle to closing the compactness sub-step of the domination
lemma is item (vi), $\mathrm{hArch}$ — and the user's rule blocks adding it
as a hypothesis.

## 5. What we have tried

1. **Direct propagation of $\mathrm{hArch}$.** Adding $\mathrm{hArch}$ as a
   parameter to the domination lemma and threading it up through P3, P4, …,
   P8. This matches the existing project pattern but violates the user's
   rule under the strict reading.

2. **Internal construction via principal-pair extraction.** Works for items
   (i), (iii), (iv), (v) but does not avoid (vi).

3. **Reformulating the half-space as a rational open** (see §4.2). Works
   for the geometric setup but still routes through the same compactness
   theorem.

4. **Stating the compactness as a hypothesis** rather than the principal-pair
   data. This just relocates the problem — somewhere a Lean witness for
   $\mathrm{IsCompact}\,K^+$ must be produced, and the only project-available
   route requires $\mathrm{hArch}$.

5. **Looking for an alternative compactness route in the project.** The
   project has compactness of $\mathrm{Spa}$ in the discrete case
   (no $\mathrm{hArch}$ needed) and in the Tate-with-$\mathrm{hArch}$ case;
   nothing in between.

## 6. Where we're stuck

**Stuck point 6.1.** *Discharging the compactness assumption for the
domination lemma without adding $\mathrm{hArch}$ as a hypothesis.*

The user's rule is strict: the result is true without $\mathrm{hArch}$
mathematically, so it can't be added. The project's only compactness
theorem requires it. The proof method (round-20 reviewer prescription)
needs compactness. Three logical paths out:

(a) Refactor the project's Spa compactness infrastructure to avoid
$\mathrm{hArch}$ — substantial work, probably requires re-doing the
closed-image description.

(b) Accept $\mathrm{hArch}$ as a permitted hypothesis on the grounds that
the project's eventual Tate-acyclicity statement already assumes it (via
propagation through the existing chain).

(c) Find a different proof method for the domination lemma that does not
go through Spa compactness.

We don't know which is the right call.

## 7. Reference to Wedhorn 8.28(b)

Wedhorn's actual proof of 8.28(b) does not explicitly invoke
mul-archimedean. He uses Spa compactness (his Theorem 7.31) freely, and his
proof of 7.31 (via Tychonoff on a spectral embedding) also makes no
explicit mul-archimedean restriction. We do not understand why the
project's Lean formalisation of Spa compactness needs $\mathrm{hArch}$ while
Wedhorn's text does not. This is part of question Q3 below.

## 8. Questions

**Q1 (the immediate blocker).** Given the situation in §4: which path
forward do you recommend — (a) refactor project compactness infrastructure
to drop $\mathrm{hArch}$, (b) accept $\mathrm{hArch}$ as a permitted
hypothesis (over-riding the strict reading of the user's rule), or (c) a
different proof method for the domination lemma that does not go through
Spa compactness? If (c), what is the alternative method?

**Q2 (the $\mathrm{hArch}$ status).** Is $\mathrm{hArch}$ — the assumption
that every $v \in \mathrm{Spv}(A)$ has a multiplicatively archimedean value
group — a *genuine* restriction in Wedhorn's 8.28(b), or is it an artifact
of one particular Lean formalisation of Spa compactness? If genuine: what
goes wrong in 8.28(b) for higher-rank valuations? If artifact: what is the
correct formulation of Spa compactness that avoids it?

**Q3 (Wedhorn's compactness route).** Wedhorn's Theorem 7.31 proves Spa
compactness for Tate rings via an embedding into a closed subset of
$\prod_{r \in A \times A} \{0, 1\}$ and Tychonoff. What is the cleanest Lean
rendering of this proof that does not need $\mathrm{hArch}$? Specifically:
in Wedhorn's argument for the closed-image step (showing $\mathrm{Spa}$'s
image in the Boolean cube is closed), where does mul-archimedean enter, if
at all?

**Q4 (reformulating P3 to avoid compactness).** Is there a different
mathematical form of the domination lemma — or of P3 itself — that avoids
compactness entirely? For instance: can the FG generators of $L.P.I^N$ be
chosen *adaptively* (depending on the half-space) so that the domination
inequality $v(b) \leq v(a)$ holds by an algebraic identity rather than a
uniform estimate? Or: can the `hopen` proof in P3 be rerouted so that we
don't need every $b \in L.P.I^N$ to satisfy $v(b) \leq v(L.s \cdot h)$ —
maybe only a finite subset suffices?

**Q5 (user-rule interpretation).** The user's binding rule reads: *"you can
only add a hypothesis if the result is false without it"*. Is the
project-pattern practice of propagating $\mathrm{hArch}$ — which is needed
by the only available proof route, even though the result is mathematically
true without it — a *violation* of this rule or a *legitimate exception*
(because the alternative is unbounded infrastructure work to refactor
compactness)? We are not asking you to arbitrate between us and the user;
we are asking: in your judgement as a working mathematician/formaliser,
which interpretation does the spirit of the rule support?

## 9. What we ask you to produce

A short reply addressing Q1–Q5. The most useful single output would be:

- A direct recommendation on Q1 (which of (a), (b), (c)).
- If (b): one sentence on whether you agree the user's rule should bend in
  this specific case.
- If (a) or (c): a high-level sketch of the alternative.
- A clarification on Q2 (genuine vs artifact).
- For Q4: even a no-it-doesn't-work answer is useful (so we stop searching).

Length budget: as long as needed; tighter is better.

## 10. Document metadata

- Project name: Adic spaces (Lean 4 formalisation following Wedhorn).
- Brief generated: 2026-05-16 (round 21).
- Length: ~5 pages.
- Build status: clean, 8 sorries in the Tate-acyclicity residuals file
  (one of which is the domination lemma; the rest are `P4`–`P8`
  substantive Wedhorn content and one Mathlib external dependency).
- Recent context: round 20 (2026-05-16) prescribed the domination-lemma
  approach for P3; this round 21 asks about the compactness sub-step's
  infrastructural blocker.
