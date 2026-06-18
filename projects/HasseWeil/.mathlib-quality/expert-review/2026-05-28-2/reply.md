# Reviewer reply — Round 6 (2026-05-28)

I reviewed the current Round 6 placeholder-audit brief. Some earlier uploaded files have expired on my side; I'm relying on the current upload and the visible prior snippets. Reupload older artifacts only if you want a strict line-by-line comparison.

## Bottom line

The placeholder pattern is not just "messy scaffolding"; it is **semantically poisonous** once the object is named `Isogeny`. Since `degree`, `sepDegree`, and `pullback` are available to downstream code, a fake pullback can silently make false theorems type-check. Your own brief shows exactly that: `isogOneSub α` has the correct point map but identity pullback, so its degree is forced to be (1), and this produced false statements such as `pointCount E = 1` in the dead chain.

My recommendation is **Strategy B as the immediate cleanup**: delete the placeholder `Isogeny` records and replace them with bare point-map data where only the point map is needed, and with genuine isogenies where degree/pullback is needed. Keep the deeper structural-enforcement refactor for later. Your brief already notes that most references only use the point-map side, while only a small number consume pullback/degree; that makes Strategy B mechanically large but conceptually safest.

---

## Q1 — Is the placeholder pattern pathological?

Yes, for anything exposed as an `Isogeny`.

There are two different issues:

1. **Lean-kernel validity.** Lean is not inconsistent: a record with an identity pullback and a separately supplied point-map is just a record. Theorems about that record may still be valid relative to its actual fields.

2. **Mathematical interpretation.** Calling that record an `Isogeny` means users expect the pullback and point-map to describe the same morphism. If they do not, any theorem using degree or pullback can become a theorem about the wrong map.

So the pattern is acceptable only if the object is clearly named as non-semantic scaffolding, for example:

```lean
structure PointEndomorphismData where
  toAddMonoidHom : E.Point →+ E.Point
```

or

```lean
structure PreIsogeny where
  pullback : ...
  pointMap : ...
  -- no semantic claims, no degree API
```

But it should **not** be an inhabitant of the same `Isogeny` type used for degree, separability, kernel-degree statements, or final theorem consumers.

A referee would not accept a formalisation where a theorem about actual isogenies goes through a hybrid object whose unused field is known false. They might accept a deliberately partial scaffold if it is quarantined under a name like `Fake`, `Raw`, `Unchecked`, or `PointMapOnly`, and if no public theorem treats it as a genuine isogeny.

For this project, the dead chain should be retired or moved under an explicitly unsafe namespace. The live `hasse_bound_skeleton` / witness-parametric chain is the right public API, because it routes through genuine `1−π` with a real pullback.

---

## Q2 — Right pullback for general `1 − α`

Use a **witness-parametric addition-pullback API**.

The best Lean pattern is not to define a total

```lean
isogOneSub : Isogeny E E → Isogeny E E
```

unless you can always construct the genuine pullback. Instead define something like:

```lean
structure AddIsogData (α β : Isogeny E E) where
  pullback : K(E) →ₐ[K] K(E)
  pointMap_eq : ...
  compat_x : pullback x = addPullback_x α β
  compat_y : pullback y = addPullback_y α β
  injective : Function.Injective pullback
  ...
```

Then:

```lean
def addIsog (h : AddIsogData α β) : Isogeny E E
```

For `1 − α`, use `addIsog` on `(id, -α)` only when the required data are available.

That gives three clean layers:

1. **Point-map only layer** for facts that only need (P\mapsto P-\alpha(P)).
2. **Genuine isogeny layer** when you have the addition-pullback data.
3. **Witness-parametric theorem layer** where general statements take the genuine pullback as an input.

Pic⁰ is not the right way to define the pullback of `1 − α` in general. Pic⁰ is good for duality and functoriality, but the concrete pullback of a sum of morphisms is naturally given by the elliptic addition morphism. For formalisation, the addition-pullback construction is the right general mechanism; when it is not available, keep the statement witness-parametric.

So I recommend:

```text
Specific α = π_q: use isogOneSub_negFrobenius W hq.
Specific α = [n]: use multiplication/division-polynomial construction.
General α: no total fake Isogeny; require AddIsogData / genuine pullback witness.
```

---

## Q3 — `hq` threading strategy

Do **not** hide `hq` inside the definition if the construction genuinely depends on it. Also do not introduce a bespoke typeclass unless it is used widely outside this one family.

Use this split:

### For genuine isogenies

Make `hq` explicit:

```lean
isogOneSub_negFrobenius (W : WeierstrassCurve K)
    (hq : 2 ≤ Fintype.card K) : Isogeny ...
```

That is honest and stable.

### For point-map-only usage

Avoid `hq` entirely by not building an `Isogeny`:

```lean
oneSubFrobeniusPointMap :
  E.Point →+ E.Point :=
AddMonoidHom.id _ - (frobeniusIsog W).toAddMonoidHom
```

This handles the ~150 sites that only need the group hom.

### For call-site convenience

Add a small local lemma or wrapper:

```lean
theorem finite_field_card_ge_two
    [Field K] [Fintype K] : 2 ≤ Fintype.card K := ...
```

and perhaps:

```lean
noncomputable def isogOneSub_negFrobenius_auto
    (W : WeierstrassCurve K) [Field K] [Fintype K] :
    Isogeny ... :=
isogOneSub_negFrobenius W (finite_field_card_ge_two K)
```

But I would keep the main theorem statements with explicit `hq` if they are already structured that way. Explicit `hq` is a small cost compared with the cost of hidden noncomputable synthesis confusing unification later.

So: **explicit `hq` for genuine isogenies, no `hq` for point-map-only objects, optional `_auto` wrapper for ergonomics.**

---

## Q4 — Should `Isogeny` enforce pullback/point-map compatibility?

Eventually yes, but not as the immediate cleanup.

Adding a compatibility field to `Isogeny` is mathematically the right direction, but your proposed field

```lean
compat : ∀ P, point_map P = (pullback evaluated at P's place)
```

is not easy to state correctly for all points. Evaluation of rational functions is undefined at poles, and for projective points one should talk about local rings, places, or projective coordinates. This is essentially a curve/function-field functoriality theorem.

If you add a weak or badly stated compatibility field, you may create more pain than it prevents.

Immediate recommendation:

1. Keep current `Isogeny` for now.
2. Add a predicate:

```lean
structure IsGenuine (φ : Isogeny E E') : Prop where
  -- pullback and point map come from the same morphism
  ...
```

or several specialised predicates:

```lean
IsGenuineAddIsog
IsGenuineFrobenius
IsGenuineMulByInt
```

3. Require `IsGenuine φ` in any theorem that transfers between point maps and pullbacks/degrees.

Longer term, split the types:

```lean
RawIsogeny       -- independent fields, no semantic guarantees
Isogeny          -- genuine, compatible
PointHomOnly     -- just AddMonoidHom
```

Then migrate public theorems to the genuine type. That is better than immediately rewriting all infrastructure around a difficult compatibility predicate.

So Q4's answer: enforce compatibility in the long run, but start with **type separation and quarantining**, not a massive one-shot structure rewrite.

---

## Q5 — How to audit compositional placeholders

Yes, composed placeholders propagate the lie.

If `φ.pullback = AlgHom.id`, then for any `ψ`:

```lean
(φ.comp ψ).pullback = ψ.pullback.comp φ.pullback
```

or the corresponding contravariant order will inherit an identity factor. Depending on composition order, this can make the composed pullback wrong while the point-map still looks plausible.

A systematic audit should be graph-based, not just grep-based.

### 1. Tag all suspect constructors

Create a namespace or attribute for constructors known to be placeholder-bearing:

```lean
attribute [placeholder_isogeny] isogOneSub isogSmulSub oneSubFrobeniusIsog
```

Or if attributes are inconvenient, create explicit "nope" lemmas:

```lean
theorem isogOneSub_pullback_placeholder :
  (isogOneSub α).pullback = AlgHom.id _ _ := rfl
```

Then grep for these constructors flowing into:

```text
.degree
.sepDegree
.pullback
.toAlgebra
.comp
.kernel  -- only if kernel is later compared to degree
isogTrace
traceOfFrobenius
pointCount_eq
hasse_bound
```

### 2. Build a dependency closure

Search for every theorem whose proof or statement mentions a placeholder constructor. Classify each occurrence:

* **point-map only**: safe after replacing with bare `AddMonoidHom`;
* **pullback/degree/sepDegree/isogTrace**: unsafe;
* **composition involving placeholder**: unsafe unless only point-map projected later;
* **statement about the placeholder as an `Isogeny`**: suspicious even if proof uses only point-map.

### 3. Add negative tests

For each placeholder, prove a pathology lemma and mark it as a linter target:

```lean
example : (isogOneSub α).degree = 1 := rfl
```

Then any theorem implying, for example,

```lean
(isogOneSub (frobeniusIsog W)).degree = pointCount W
```

should be considered suspect unless it uses the genuine replacement.

### 4. Retire or rename dead APIs

Move dead declarations under:

```lean
namespace Deprecated
namespace Placeholder
```

and add docstrings:

```lean
/-- Do not use in mathematical theorems. Pullback is deliberately fake. -/
```

If possible, make them `private` or `@[deprecated]`.

### 5. Public theorem audit

The most important audit is public-facing theorem names. Your brief says both a dead `hasse_bound` and live `hasse_bound_skeleton` compile, so downstream users can choose the wrong one. I would immediately rename the dead theorem:

```lean
deprecated_hasse_bound_false_placeholder
```

or move it out of the public import path. A sorry-bearing false statement should not share a plausible theorem name.

---

## Strategy choice among A/B/C

Choose **Strategy B** now.

### Why B?

* It removes the bad semantic object.
* It keeps the genuine route honest.
* It avoids a project-wide compatibility refactor.
* It matches the actual usage pattern: most sites only need the point-map, and the few that need real isogenies can use `isogOneSub_negFrobenius W hq`.

### Why not A?

Strategy A keeps the dangerous name and a partially fake general API. For general `α`, it still cannot construct the real pullback. That means either more sorries inside the constructor or more fake behaviour. It is too easy to regress.

### Why not C immediately?

C is the right long-term design, but it is expensive. It requires formalising the compatibility between function-field pullbacks and point maps, which is itself nontrivial. Do not block cleanup on it.

So the pragmatic plan is:

```text
1. Delete/retire placeholder Isogeny constructors.
2. Replace point-map-only uses with bare AddMonoidHom.
3. Replace genuine uses with isogOneSub_negFrobenius W hq or future AddIsogData.
4. Add IsGenuine predicate and require it where point-map/pullback transfer is used.
5. Later, refactor Isogeny itself if the compatibility API stabilises.
```

---

## Final recommendation

Perform the cleanup in this order:

1. **Quarantine dead theorems**: move/rename `hasse_bound`, `pointCount_eq`, `traceOfFrobenius_sq_le` if they depend on placeholder degree.
2. **Introduce point-map-only definitions** for `id − π` and `rπ − s`.
3. **Replace the 150 point-map-only call sites** with point-map data.
4. **Replace the ~4 degree/pullback call sites** with genuine isogenies or witness-parametric hypotheses.
5. **Add a linter-style audit script** for placeholder names flowing into `.degree`, `.sepDegree`, `.pullback`, `.toAlgebra`, `isogTrace`, and `.comp`.
6. **Only later** consider strengthening the `Isogeny` structure itself.

This is not just hygiene. It is necessary to preserve trust in the formalisation: a record called `Isogeny` with a known-false pullback should not be used in public theorem statements, even if many individual field projections happen to be harmless.
