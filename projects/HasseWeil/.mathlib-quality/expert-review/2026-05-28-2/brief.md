# Review brief (round 6) — Hasse bound formalization: structural placeholder removal + V.1.3 status update

*Prepared 2026-05-28 for the same arithmetic-geometry reviewer as rounds 1–5.
Self-contained; no repository access required. Round 5 (2026-05-28) reported
the V.1.3 RouteB B2 finding (the `(rX − rXq)² ∣ nReduced_R` residual is
universally false) and you recommended Option I′ (function-field map +
projective/local fibre compatibility). We applied the Option I′ retraction
of the CoordHom-side chain and documented the L6_B3_tower path. **In the
follow-up audit we found a more systemic issue**: three load-bearing
"placeholder" isogeny definitions that pair a correct `toAddMonoidHom` with
a deliberately-incorrect `pullback := AlgHom.id`, enabling several
universally-false statements to compile. This brief explains the
placeholder design, lists the false statements it has produced, gives the
40-file blast-radius for any clean removal, and asks for guidance on the
cleanest way to eliminate this pattern from a formal-proof project. We
also update the V.1.3 status under the live witness-parametric chain.*

---

## 1. The two problems, briefly

**Problem A (structural — the focus of this round).** Three definitions in
the project (`isogOneSub α`, `isogSmulSub α r s`, `oneSubFrobeniusIsog W`)
package an `Isogeny` data structure whose `pullback` field is the
*identity* algebra-hom on the function field, while the `toAddMonoidHom`
field is mathematically correct. The `Isogeny` structure does not enforce
compatibility between these two fields. Downstream theorems that touch
the `pullback` (or the `degree`, which is derived from the pullback)
consequently assert universally-false statements while still type-checking.

**Problem B (V.1.3 closure — round-5 follow-up).** The retraction of the
CoordHom-side chain landed and the L6_B3_tower path is now isolated as
the live route. V.1.3 reduces to a single concrete residual: every prime
of the integral-closure data `S` over the prime `(X)` is the place at
some `F_q`-rational kernel point of `1 − π_q`. This is essentially the
K-level analogue of Silverman II.2.4 for the pole-locus of
`f = (1 − π_q)*x`. No new mathematical obstacle relative to round 5; the
problem is now purely the place ↔ closed-point dictionary over a finite
base field.

The bulk of this brief is **Problem A**.

---

## 2. The placeholder design and why it produces false statements

### 2.1. The data structure

The project's `Isogeny` data carries two independent fields, modelling the
two pieces of data attached to an isogeny `φ : E → E'`:

> An *isogeny* `φ : E_1 → E_2` is given by:
> * a function-field pullback `φ^* : K(E_2) → K(E_1)` (an injective
>   `K`-algebra map, dual to the geometric morphism);
> * a group homomorphism on `K`-rational points `φ : E_1(K) → E_2(K)`.

These two pieces are *coupled* mathematically: each determines the other
when the curve is geometrically integral. But the formalisation carries
them as independent record fields with no enforced compatibility.

### 2.2. The placeholder definition

For `α` an isogeny `E → E`, the project defines `1 − α` as

> *(Placeholder definition.)* `isogOneSub α` is the isogeny whose
> *pullback* is the identity map `K(E) → K(E)` and whose *point-map* is
> `id − α` on `E(K)`.

The point-map field is genuinely the group hom representing `P ↦ P − α(P)`.
The pullback field is the algebra-hom for the identity endomorphism of `E`,
not the algebra-hom for `1 − α`. The author chose this because the
genuine `pullback` for `1 − α` requires the addition-formula machinery in
the function field, which the project formalised later.

Two further placeholders share the same flaw:
* `isogSmulSub α r s` (purports to model `r·α − s·1` for integers `r, s`);
* `oneSubFrobeniusIsog W = isogOneSub (π_q)` (specialises the above to the
  Frobenius).

### 2.3. The concrete consequences

The degree of an isogeny is defined as `[K(E_1) : φ^* K(E_2)]`, computed
from the pullback. Since the placeholder's pullback is the identity:

> `(isogOneSub α).degree = [K(E) : K(E)] = 1` for every `α`.

Three downstream theorems are then declared whose statements unfold to
false claims:

> **(Failed theorem A.)** `pointCount E = q + 1 − tr(π)` where
> `tr(π) = 1 + deg(π) − deg(isogOneSub π) = 1 + q − 1 = q`. Conclusion:
> `pointCount E = 1`.
>
> **(Failed theorem B.)** `(traceOfFrobenius)² ≤ 4q`, where
> `traceOfFrobenius := tr(π) = q` (per A). Conclusion: `q² ≤ 4q`.
>
> **(Failed theorem C.)** `|#E(F_q) − q − 1| ≤ 2√q`, derived from B via
> a real-valued discriminant bound.

**Concrete counterexamples**:
* Failed theorem A at `E : y² = x³ − x` over `F_5`: `#E(F_5) = 8`, not 1.
* Failed theorem B at any `q ≥ 5`: `25 > 20`, `49 > 28`, etc.
* Failed theorem C inherits the falsity.

All three are sorry-bearing — they were declared with the intention of
later supplying proofs, but the placeholder substitution makes the
declared statements false, so the sorries cannot close. **The
declarations themselves are the lies.**

### 2.4. The blast radius

The three placeholder definitions and the three failed theorems above
together appear (by name) in **40 of the project's roughly 80
mathematical files**. Most uses (~150 of ~160 textual references to
`oneSubFrobeniusIsog`) only touch the `toAddMonoidHom` field and are
mathematically correct — the placeholder's group-hom side is genuine.

Only ~4 sites consume the `pullback` or `degree` of a placeholder, and
these are precisely the artefacts where the lies enter the formal proof.

### 2.5. What the project actually contains — an honest accounting

In parallel with the placeholder chain, the project developed a
**witness-parametric chain** that bypasses the placeholders entirely.
This chain takes the *true* `1 − π_q` as an external input (the project's
`isogOneSub_negFrobenius` constructed via the addition formula on the
function field, sorry-free modulo the V.1.3 residual described in §4) and
discharges the Hasse discriminant inequality from the qf-nonneg property
of the degree quadratic form. The witness-parametric top-level
`hasse_bound_skeleton` routes through this genuine isogeny. This chain is
mathematically sound.

But it would mislead the reviewer to say "the project is ~90% sound, ~10%
dead branch". After the round-5 retraction, a more honest accounting of
the project's mathematical content is roughly:

> **(Live, load-bearing for the Hasse-bound closure path) — ~30–40%.**
> The L6 chain (`Sinf` framework, K3+K4 dispatcher, bridge lemmas
> computing `e = 2` and `f = 1` at kernel primes, kernel-to-prime
> injectivity, `l6_B3_tower` giving `[K(E) : K(f)] = 2 · deg(1 − π)`,
> the squeeze composer), Phase 1 (K̄-Frobenius fixed-locus count =
> `#E(F_q)`), L5, the witness-parametric Hasse-bound assembly, the
> shipped `isogOneSub_negFrobenius` with its genuine pullback, plus a
> handful of utility lemmas (`kernel_eq_top_of_hom_eq_id_sub_frobenius`,
> `isogOneSub_negFrobenius_isSeparable`). This is the spine that
> reaches Hasse-bound modulo two remaining leaves (V.1.3 + qf-nonneg).
>
> **(Dead chain — the placeholder artefacts) — ~10%.** Three
> placeholder definitions; three false-statement theorems; a dead
> top-level `hasse_bound` API; the WireUpPrep "CoordHom" assembly. All
> retired in spirit (round 5) but the declarations are still in the
> codebase and contribute build-load and reference-count.
>
> **(Orphaned — correct mathematics built for the dead CoordHom strategy)
> — ~40–50%.** This is the substantial cost. The KE-level chord-formula
> infrastructure (`addPullback_x`, `addPullbackNumerator_*`, slope
> analysis, the `addPullback_x_in_coordRing_range` existential, etc.);
> the R-level polynomial-identity layer (Identity A, Identity B, the
> squared-form Vieta Identity C, `nReduced_R_image_eq`,
> `pullback_equation_R`, `nReduced_R_eq_numUnreduced_R`); the
> `IsogenyFactor`-style scaffolding for factoring `1 − π_q` through
> specific isogenies. These are *correct* polynomial identities and
> KE-level chord identities — they encode true mathematics about the
> curve's structure — but they were built as steps toward the *false*
> divisibility `D² ∣ nReduced_R` (round-5 B2), and they do not feed the
> live L6_B3_tower path. About 24 deep-pass dispatches of careful work
> sits here.
>
> **(Reusable scaffolding) — ~10%.** The base-change machinery
> (`degree_oneSubFrob_baseChange_eq`, the tensor-product / function-field
> base-change apparatus), parts of WireUpPrep, the IsAlgClosed-free
> smooth-point extraction engine. Currently unused on the live path but
> might find a role under the round-5 Option I′ if a K̄ base-change is
> threaded into the K-level place-vs-closed-point bijection.

So the project has two parallel top-level Hasse-bound statements:
* `hasse_bound` (the dead chain, sorry-bearing on false statements);
* `hasse_bound_skeleton` (the live chain, sorry-free body modulo two
  GAP leaves).

The fact that *both* compile means a downstream user can pick the wrong
one and get a false-statement-bearing dependency without warning. Beyond
that, the orphaned middle band (the ~40–50%) is a real cost: it is the
mathematical work that the dead CoordHom strategy generated as a
by-product. The identities are true, but they don't advance the goal.

The Q6 question we add to §7 below ("salvage on the orphaned middle")
reflects this honestly: is there *any* role the orphaned KE-level chord
identities and R-level polynomial identities can play in the live
L6_B3_tower / Option I′ path, or do we accept them as sunk cost?

---

## 3. The mathematical setting (recap from rounds 1–5)

For completeness; the reviewer who has been following along can skip this
section.

* `K = F_q` a finite field with `q = p^n` elements;
* `E` an elliptic curve over `K` in Weierstrass form
  `y² + a_1 xy + a_3 y = x³ + a_2 x² + a_4 x + a_6` with discriminant
  `Δ ≠ 0`;
* `R = K[X,Y]/(W(X,Y))` is the affine coordinate ring of `E`;
* `K(E) = Frac(R)` the function field;
* `π_q : E → E` the `q`-power Frobenius isogeny;
* `1 − π_q : E → E` the isogeny whose kernel as a group scheme is
  `E(F_q)`.

**Target.** Hasse's theorem: `|#E(F_q) − (q+1)| ≤ 2√q`.

**Strategy.** The witness-parametric skeleton reduces this to two leaves:

> **(V.1.3 leaf.)** `deg(1 − π_q) = #E(F_q)`. Silverman III.5.5 via
> III.4.10(c) for separable isogenies.

> **(III.6.3 leaf.)** For all `(r, s) ∈ ℤ²`, the integer
> `Q(r, s) := q r² − tr(π_q) · rs + s²` is `≥ 0` (the degree quadratic
> form on `End(E)` is positive semidefinite).

Both leaves feed into a witness-parametric assembly that proves the
discriminant bound `tr(π_q)² ≤ 4q` and hence the Hasse inequality.

---

## 4. Status update on V.1.3 (the round-5 follow-up)

We applied the round-5 plan to retract the dead CoordHom-side chain and
document the L6_B3_tower path. The reduction structure now looks like:

> V.1.3 (`deg(1 − π_q) = #E(F_q)`)
>
> ⇕ (via separability `sepDeg = deg` and `# ker = #E(F_q)` from the
>    kernel-is-rational-locus fact, both axiom-clean)
>
> the K-level prime sum identity:
>
> > For the integral closure `S` of `K[X]` inside `K(E)` under
> > `X ↦ 1/f` (where `f = (1−π_q)*x`), every prime of `S` over `(X)`
> > equals `P_T := bridge(T)` for some `T ∈ ker(1 − π_q)`.

Combining this with:
* The shipped *kernel-prime contribution* (each kernel-prime has
  ramification index `2` and inertia degree `1`, axiom-clean);
* The shipped *kernel-to-prime injection* (`Sinf_kernelToPrime_injective`,
  axiom-clean);
* Mathlib's `Ideal.sum_ramification_inertia` (the fundamental identity
  `Σ_P e_P · f_P = [Frac(S) : K(X)]`);
* The shipped `[K(E) : K(f)] = 2 · deg(1 − π_q)` (`l6_B3_tower`,
  axiom-clean);

we get V.1.3 axiom-clean, modulo the bullet displayed above. The
mathematical content of that bullet (Silverman II.2.4 specialised to the
pole-locus of `f`): every closed point where `f` has a pole corresponds to
a closed point of `E` where `1 − π_q` sends to the point at infinity, which
is precisely the kernel locus, and over `K = F_q` every kernel point is
`K`-rational (no Galois orbits of size > 1 since the geometric kernel
`E(F_q) ⊂ E(K̄)` is itself the image of `K`-rational points).

The project's `smoothPointEquivHeightOneSpectrum` ships the
place ↔ closed-point bijection only over algebraically closed `L`. The
`K`-level analogue restricted to the pole locus of a specific `f` is the
single new piece of infrastructure V.1.3 still needs. We are deferring
that to a focused session.

**No new mathematical obstacle on V.1.3**; the reformulation is mechanical
once we have the K-level bijection content. The reviewer's Option I′ in
round 5 anticipated exactly this.

---

## 5. The III.6.3 leaf — also blocked by a placeholder

The qf-nonneg leaf is currently parametric over an existence witness:
*for every `(r, s) ∈ ℤ²` with `(r, s) ≠ (0, 0)`, there is an isogeny
whose degree equals `Q(r, s)`*. The witness in turn reduces to the
"degree quadratic form" identity: `deg(r · π_q − s · 1) = q r² − tr(π_q) rs + s²`,
which Silverman III.6.3 proves via the Pic⁰ pivot (the bilinearity of the
degree pairing on `End(E)`).

The project has a *genuine* isogeny `r · π_q − s · 1` via composition
(`genuineIsogSmulSub W r s`) when both `r` and `s` are nonzero mod the
characteristic; the placeholder `isogSmulSub α r s` (with
`pullback := AlgHom.id`) is the placeholder we want to eliminate.

The III.6.3 closure still requires the Pic⁰-pivot witness
`(rV − s) · (rπ − s) = [Q(r, s)]` at the isogeny level (where `V` is
Verschiebung), which is its own non-trivial leaf. Not the focus of this
brief.

---

## 6. The cleanest fix: candidate strategies

We see three candidate strategies, with the following trade-offs.

### 6.1. Strategy A — replace the placeholder body, keep the signature

Modify `isogOneSub α` to construct the *genuine* pullback when one is
constructible, raising a `sorry` otherwise. For the `α = π_q` case,
substitute the genuine `isogOneSub_negFrobenius` (which uses the
addition-formula pullback).

Pros: minimal call-site impact (~40 files unchanged in signature).

Cons: `isogOneSub_negFrobenius` requires a hypothesis `2 ≤ q`. This is
derivable from `Field K + Fintype K` via `Fintype.one_lt_card_iff_nontrivial`,
but threading it through is a project-wide effort. Also, for general `α`
that isn't Frobenius (e.g. `α = mulByInt n`), there's no `addPullback`
infrastructure yet, so `sorry` remains.

### 6.2. Strategy B — delete the placeholder, replace with bare data

Delete `isogOneSub`, `isogSmulSub`, `oneSubFrobeniusIsog` as `Isogeny`
records entirely. For the ~150 sites that only need the `toAddMonoidHom`
part, replace `(oneSubFrobeniusIsog W).toAddMonoidHom` with the bare
`AddMonoidHom.id − (frobeniusIsog W).toAddMonoidHom`. For the ~4 sites
that need a real `Isogeny`, replace with `isogOneSub_negFrobenius W hq`
(threading `hq`).

Pros: eliminates the pathological pattern completely.

Cons: substantial mechanical refactor across 40 files. Some lemma
signatures change.

### 6.3. Strategy C — enforce compatibility in the data structure

Add a third field to `Isogeny` (or replace with a `Prop`-bundled
structure) requiring that the pullback and point-map correspond to the
same geometric morphism. Then the placeholder cannot be constructed
because it fails the compatibility check.

Pros: makes the pathological pattern *impossible* by design.

Cons: requires rewriting ~all of the project's `Isogeny` infrastructure.
The compatibility predicate is non-trivial (it's the curve ↔ function-field
functorial faithfulness — Silverman II.2.4).

---

## 7. The questions for you

The first four are user asks; the fifth is agent-surfaced.

**Q1 — Is the placeholder pattern pathological?** In a formal-proof
project where a data structure has multiple fields with no enforced
compatibility (e.g. our `Isogeny` carrying `pullback` and
`toAddMonoidHom` as independent records), is the pattern "pair a *correct*
field with a *deliberately incorrect* other field" categorically illegal,
or is it acceptable scaffolding when downstream callers only use the
correct field? In particular: would a referee accept a paper claiming a
formalised theorem `P` whose proof goes through such a hybrid object, if
the hybrid object's only-used field is correct and the unused field is a
known lie? Is there a body of work in the formal-proof literature on the
right hygiene here?

**Q2 — Right pullback for general `1 − α`?** We have the genuine pullback
for two specific cases: `α = π_q` (via the addition formula in the
function field, axiom-clean), and `α = [n]` (multiplication by `n`, via
division polynomials). For *general* `α`, what is the right
Lean-formalisable construction of the pullback of `1 − α`? Options we see:
* Routing through Pic⁰ and the universal property of the Picard scheme.
* Building the addition pullback as a function of two general isogenies
  `α, β`, then specialising to `(α, 1)`.
* Accepting that only specific `α` have genuine pullbacks and refactoring
  the project's API so general-`α` claims are always witness-parametric
  (taking the genuine pullback as data).

Which of these is the right Lean approach in your experience?

**Q3 — `hq` threading strategy.** The genuine `isogOneSub_negFrobenius`
requires `hq : 2 ≤ Fintype.card K`. This is derivable from `Field K +
Fintype K` (via `Fintype.one_lt_card_iff_nontrivial`), but Lean's
elaboration doesn't auto-derive it. Should we:
* (a) add `hq` as an explicit parameter to `oneSubFrobeniusIsog`
  everywhere (~160 call sites to thread);
* (b) derive `hq` inside the definition (signature unchanged, but the
  definition is now `noncomputable` due to the existence of the derived
  hypothesis); or
* (c) something else (e.g. a typeclass `[NontrivialFinite K]` that
  packages both `Field` and `Fintype` and the cardinality bound)?

**Q4 — Structure-level enforcement.** Would you recommend that we *change
the `Isogeny` data structure itself* to enforce pullback / point-map
compatibility — for instance by adding a `Prop`-valued field
`compat : ∀ P, point_map P = (pullback evaluated at P's place)` — so that
placeholders of this kind become impossible to construct? Or is this
over-engineering for what is, in essence, a project hygiene issue rather
than a structural one?

**Q5 (agent-surfaced) — Compositional placeholders elsewhere?** We have
verified that `Isogeny.kernel`, `.degree`, `.sepDegree`,
`.toAddMonoidHom`, and the composition `Isogeny.comp` operate in a way
that is mathematically sound when the input isogeny IS genuine. The
question we did not check thoroughly: are there other constructions in
the project that propagate a placeholder's lie? E.g.,
`oneSubFrobeniusIsog.comp ψ` for some `ψ` — does the composed
`pullback` inherit the identity-map placeholder lie in a way that other
parts of the project consume? If so, the cleanup we are planning will not
be complete. Is there a systematic way to audit this beyond grepping for
`.pullback` and `.degree` of placeholder names?

**Q6 (agent-surfaced) — Salvage on the orphaned middle.** Per the honest
accounting in §2.5, roughly 40–50% of the project's content was built for
the dead CoordHom strategy: the KE-level chord-formula infrastructure
(`addPullback_x`, the chord-numerator equations, slope analysis) and the
R-level polynomial-identity layer (the three "Vieta" identities A, B, C
plus the supporting `nReduced_R_image_eq` / `pullback_equation_R` /
`nReduced_R_eq_numUnreduced_R`). These are *correct* polynomial / KE
identities — they encode genuine algebra of the chord formula and the
Frobenius pullback — but they were derived as steps toward the *false*
`D² ∣ nReduced_R` divisibility (round-5 B2), and they do not feed the
live L6_B3_tower path.

Is there *any* role this orphaned infrastructure can play in the live
chain, the V.1.3 closure, or the III.6.3 closure (cf. §5)? Concretely:

* Can the KE-level chord identities feed the K-level place ↔ closed-point
  bijection needed for V.1.3 (e.g., by characterising the pole-locus of
  `f = (1 − π_q)*x` directly)?
* Can the R-level Vieta identities (A, B, C) be repurposed for the III.6.3
  Pic⁰-pivot witness — e.g., to verify the degree identity
  `deg(r π − s · 1) = q r² − tr(π) rs + s²` at the polynomial level for
  small `(r, s)`, building toward the general identity?
* Or do we accept the orphaned middle as sunk cost and proceed with the
  live chain alone?

Any pointers to "this was actually the wrong way to attack but here's how
to recover" arguments in the formal-proof literature would also help —
the project has invested heavily in the addition-pullback-in-`R` line of
reasoning, and we want to be sure we are not throwing away more than is
necessary.

---

## 8. Document metadata

- Project: Hasse bound for `E/F_q`, Lean 4 / Mathlib.
- Round: 6 (rounds 1–3 on `qf_nonneg`; round 4 chose Route B for V.1.3;
  round 5 issued the V.1.3 RouteB B2 finding; round 6 is the structural
  placeholder audit).
- Build status: compiles cleanly (3019 jobs); two B2-recognised
  false-statement theorems (`traceOfFrobenius_sq_le`, `pointCount_eq`)
  remain in the codebase as sorry-bearing dead code; `hasse_bound_skeleton`
  is the live top-level API.
- Salvageable infrastructure: an honest accounting (§2.5) puts roughly
  30–40% of the project on the live path to Hasse-bound closure; ~10%
  is the dead placeholder chain; **~40–50% is correct mathematics
  orphaned by the round-5 B2 retraction of the CoordHom strategy**; and
  ~10% is base-change / scaffolding that may find a role under Option I′.
  This is a non-trivial sunk cost and §7 Q6 asks the reviewer whether
  any of the orphaned middle can be reused.
- Counterexample audit-trail: three B2 entries in the project-internal
  log (`nReduced_R_div_D_sq`, `pointCount_eq`, `traceOfFrobenius_sq_le`).
