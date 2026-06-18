# Worker brief — T-HASSE-CLOSE-C (Dual existence, Route A)

**For**: the CLOSE-C worker
**Status of scaffold**: COMPLETE and axiom-clean (11 theorems, 307 lines in
`HasseWeil/DualIsogeny/RouteA.lean`)
**Status of closure**: BLOCKED on 4 specific upstream witnesses (see §3)
**Goal**: discharge the sorry at `HasseWeil/DualIsogeny.lean:142`
(`exists_dual : ∀ α, ∃! β, IsDualOf E β α`)

---

## 1. TL;DR — what you're building

The scaffold is done. You need to produce 4 specific witnesses for **every
α : Isogeny E E**, then assemble them via the existing closer
`exists_dual_of_route_A_raw_witness`. That's it.

```lean
-- Already shipped, axiom-clean, in HasseWeil/DualIsogeny/RouteA.lean:
theorem exists_dual_of_route_A_raw_witness
    (α : Isogeny E E)
    (lamPb : E.FunctionField →ₐ[F] E.FunctionField)
    (h_pb : (mulByInt E α.degree).pullback = α.pullback.comp lamPb)
    (lamHom : E.Point →+ E.Point)
    (h_hom : (mulByInt E α.degree).toAddMonoidHom = lamHom.comp α.toAddMonoidHom)
    (h_α_surj : Function.Surjective α.toAddMonoidHom)
    (h_pb_comm : α.pullback.comp (mulByInt E α.degree).pullback =
      (mulByInt E α.degree).pullback.comp α.pullback) :
    ∃! β : Isogeny E E, IsDualOf E β α
```

Your job is to **construct the four `lamPb, h_pb, lamHom, h_hom` and the two
`h_α_surj, h_pb_comm`** for any α (with appropriate degree/separability
hypotheses), then wire it into `exists_dual`.

---

## 2. Read these files first (in order)

1. `HasseWeil/DualIsogeny/RouteA.lean` — the scaffold. Every step (1–6) is
   documented and proved as a witness form.
2. `HasseWeil/DualIsogeny.lean:142` — the sorry you're closing.
3. `HasseWeil/EC/IsogenyFactor.lean` — has `factor_through_isogeny_witness` +
   `factor_unique_of_surjective`. These are your packaging tools.
4. `HasseWeil/EC/IsogenyKernel.lean` — has the kernel theory. Critical:
   `card_kernel_eq_degree_of_separable_witness` (T-III-4-015 witness form,
   ALREADY axiom-clean).
5. `.mathlib-quality/tickets/close/T-HASSE-CLOSE-C-dual-existence.md` — the
   full ticket with progress log.

---

## 3. The four upstream witnesses (your deliverables)

For each α : Isogeny E E (with α.degree ≠ 0 and appropriate separability):

### 3.1 — `lamPb` + `h_pb` (the pullback factor)

```lean
∃ lamPb : E.FunctionField →ₐ[F] E.FunctionField,
    (mulByInt E α.degree).pullback = α.pullback.comp lamPb
```

**Mathematical content**: this is **Silverman III.4.11 / T-III-4-016
unconditional** — the factorization theorem at the function-field level.

**Strategy**: when `ker α ⊆ ker [deg α]` (which holds for all α — see
`kernel_subset_kernel_mulByInt_deg_of_separable_witness` in
`RouteA.lean:104`), the pullback `α.pullback : K(E) →ₐ[F] K(E)` has image
contained in the **fixed field** `K(E)^{ker α}`. Conversely, `K(E)^{ker α}
= α.pullback.fieldRange` (Silverman III.4.10c, Galois fixed-field
characterization).

For the chain `ker α ⊆ ker [deg α]`, both `α.pullback` and `[deg α].pullback`
factor through the same Galois extension. Apply Galois descent:
`[deg α].pullback = α.pullback ∘ lamPb` for some lamPb.

**Sub-deliverables**:
- `T-III-4-015` unconditional: `Algebra.IsSeparable + Finite kernel ⇒
  Algebra.fixedField (kernel.action) = α.pullback.fieldRange`.
  This is **PARTIAL** in witness form (`card_kernel_eq_degree_of_separable_witness`);
  upgrade to unconditional needs **T-II-2-009 Piece 9** (generic fiber
  existence).
- `T-III-4-016` unconditional: `ker α ⊆ ker β ⇒ ∃! lamPb, β.pullback =
  α.pullback ∘ lamPb`. This is **PARTIAL** in witness form
  (`factor_through_isogeny_witness`); upgrade is the same Galois argument.

**Estimated effort**: 300–500 LOC.

### 3.2 — `lamHom` + `h_hom` (the point-map factor)

```lean
∃ lamHom : E.Point →+ E.Point,
    (mulByInt E α.degree).toAddMonoidHom = lamHom.comp α.toAddMonoidHom
```

**Mathematical content**: this is **Silverman II.2 / T-II-2-001** smooth-curve
duality — the dual of `lamPb` at the point-map level.

**Strategy**: every algebra hom `K(E) →ₐ[F] K(E)` corresponds to a morphism
`E → E` of curves (II.2.4 functor between curves and field extensions). The
point map of `lamPb` is your `lamHom`. The factoring identity at the
point-map level then follows from functoriality.

**Sub-deliverable**: T-II-2-001 (rational map → morphism). Currently OPEN.
Substantial: needs the curves-as-anti-equivalent-of-field-extensions theory.

**Caveat**: you may not need full T-II-2-001. For Route A, you only need to
produce a point-map factor matching the algebra-map factor. If `lamPb` is
constructed via the Galois fixed-field theorem applied to a SUBFIELD that
already corresponds to a curve (e.g. E itself), the point map exists by
functoriality of the standard equivalence. Bound: **150–300 LOC** for this
specific specialization.

### 3.3 — `h_α_surj : Function.Surjective α.toAddMonoidHom`

⚠ **STRUCTURAL WARNING**: as written, `α.toAddMonoidHom` is on `E.Point`
which (in our codebase) currently means **F-rational points**, not
`F̄`-rational points. Over `F_q` with separable α of degree > 1, this is
**FALSE on F_q-points**.

**Three resolutions** (pick one):

(a) **Re-target Isogeny.toAddMonoidHom to F̄-points**. Big refactor — touches
   `HasseWeil/Basic.lean:63` (the `Isogeny` structure) and every consumer.
   ~500 LOC of churn.

(b) **Specialize Route A to F̄ at the dual-existence level**. Define the
   dual existence over F̄ rather than F. This is closer to Silverman's
   convention. ~200 LOC.

(c) **Replace surjectivity in the uniqueness argument**. The current Route A
   uniqueness uses `h_α_surj` via `factor_unique_of_surjective`. An
   alternative uniqueness via **left + right composition** (using
   `α ∘ β = [deg α]` AND `β ∘ α = [deg α]`) avoids surjectivity. ~100 LOC,
   but requires `IsDualOf` to bundle both compositions (it already does).

**Recommended**: try (c) first. If it works, you avoid the F-vs-F̄ issue
entirely. If not, fall back to (b).

### 3.4 — `h_pb_comm : α.pullback.comp [deg α].pullback = [deg α].pullback.comp α.pullback`

**Mathematical content**: T-III-4-020 (scalar commutativity) for the
pullback. The `toAddMonoidHom` part is **already shipped** as
`mulByInt_toAddMonoidHom_comm` (RouteA.lean:150) since it's automatic from
`map_zsmul`. Only the pullback part is missing.

**Strategy**: by definition of `mulByInt n` for n ≠ 0, the pullback is
`mulByInt_pullbackAlgHom W n hn`. This algebra hom commutes with α.pullback
because both are F-algebra homs and they agree on the generators
(α-invariance under scalar multiplication).

**Estimated effort**: 50–100 LOC. Likely the easiest of the four.

---

## 4. Order of attack (recommended)

1. **Day 1 — `h_pb_comm` (3.4)**: easiest, pure algebra. ~50 LOC. Get a
   quick win and a feel for the codebase.

2. **Day 2 — `h_α_surj` resolution path (3.3)**: try option (c), the
   left+right-composition uniqueness alternative. Modify
   `dual_unique_of_surjective` in RouteA.lean to take the `IsDualOf` second
   composition as input instead of surjectivity. Should drop a sorry from
   the chain.

3. **Days 3–7 — `lamPb` + `h_pb` (3.1)**: the Galois fixed-field upgrade.
   This is the bulk of the work. You need:
   - Either upgrade `card_kernel_eq_degree_of_separable_witness` to
     unconditional (depends on T-II-2-009 Piece 9), or
   - Take T-II-2-009 Piece 9 as a hypothesis and propagate.
   - Then prove `α.pullback.fieldRange = K(E)^{ker α}`.
   - Then apply this twice (for α and [deg α]) and use `ker α ⊆ ker [deg α]`
     to get the factor.

4. **Days 8–10 — `lamHom` + `h_hom` (3.2)**: smooth-curve duality. Try the
   specialization (lamPb as Galois-extension hom whose source/target are
   already curve function fields, point map is functorial).

5. **Day 11 — final wire-up**: assemble all 4 witnesses + 2 structural
   facts, plug into `exists_dual_of_route_A_raw_witness`, close
   `DualIsogeny.lean:142`. **Verify axiom-clean.**

---

## 5. Acceptance criteria

```bash
# After your last commit:
lake env lean -c <(echo 'import HasseWeil.DualIsogeny
#print axioms HasseWeil.exists_dual')
# Expected output: [propext, Classical.choice, Quot.sound]
```

**Cascade check** — once `exists_dual` is axiom-clean:
- `isogDual_comp_self`, `self_comp_isogDual`, `degree_isogDual`,
  `isogDual_isogDual` — all already content-complete, become axiom-clean
  automatically.
- `degree_quadratic_closed` in `DegreeQuadraticForm.lean` — already
  witness-parametric; instantiate with the dual to close
  `degree_quadratic` (sorry at line 145).
- HOLE E in `Hasse/Unconditional.lean` — discharges via
  `hasse_bound_via_signed_QF` once you produce the signed QF identity from
  `degree_quadratic_closed`.

---

## 6. Pitfalls and gotchas

- **F vs F̄ points**: see §3.3. Don't get bogged down — pick option (c)
  first.
- **`exists_dual_of_construction` vs `exists_dual_of_constructor`**: the
  former is per-α, the latter is universal. Build the per-α version first
  via `exists_dual_of_route_A_raw_witness`, then lift.
- **Inseparable case**: Silverman III.6.1 has a "Case 2" using
  Frobenius-Verschiebung decomposition (T-II-2-016). For Hasse-Weil over
  F_q with Frobenius α = π, this case is non-trivial. **Recommended scope
  cut**: deliver `exists_dual` for **separable** α first; the inseparable
  case can be handled later via T-II-2-016 (factor π = π_sep ∘ Frob^k +
  Verschiebung). Note that for the Hasse bound, the relevant α is
  `frobeniusIsog W` which is purely inseparable — so the inseparable case
  IS critical for Hasse closure.
- **Build cycle gotcha**: `DualIsogeny.lean` is upstream of many files.
  Don't add imports to upstream modules — keep your work in
  `DualIsogeny/RouteA.lean` and the new infrastructure files
  (`EC/QuotientCurve.lean`, etc.).
- **No new axioms**: every theorem must depend only on
  `[propext, Classical.choice, Quot.sound]`. Use `#print axioms` after
  every named theorem. If `sorryAx` shows up, find and fix.

---

## 7. Files you'll create or modify

| File | Action | Estimated LOC delta |
|---|---|---|
| `HasseWeil/EC/IsogenyKernel.lean` | upgrade `card_kernel_eq_degree` to unconditional | +100 |
| `HasseWeil/EC/IsogenyFactor.lean` | upgrade `factor_through_isogeny_witness` to unconditional | +200 |
| `HasseWeil/EC/QuotientCurve.lean` (NEW) | Galois fixed-field for E | +300 |
| `HasseWeil/DualIsogeny/RouteA.lean` | replace `h_α_surj` with composition-based uniqueness | +50 |
| `HasseWeil/DualIsogeny.lean:142` | close `exists_dual` sorry | wire-up only |
| `HasseWeil/DegreeQuadraticForm.lean:145` | close via cascade | ~10 |
| `HasseWeil/Hasse/Unconditional.lean` | discharge HOLE E sorries | ~10 |

**Total**: ~700 LOC for the separable case. Inseparable extension: ~200 LOC
more (handles Frobenius case via T-II-2-016).

---

## 8. Coordination with parallel workers

- **CLOSE-A worker**: independently delivering HOLE D + `addPullbackAlgHom`.
  Their work doesn't block CLOSE-C; CLOSE-C doesn't block them.
- **CLOSE-B worker (Claude/me)**: parallel route via formal-group bridge.
  Either CLOSE-B or CLOSE-C closes HOLE E; whichever lands first wins.
  No coordination needed; they don't share files.
- **worker-A** (`infra/`): may deliver T-II-2-009 Piece 9 separately.
  If they land it before you need it, your §3.1 work simplifies.

---

## 9. If you get stuck

- The four upstream witnesses (§3) are **independently** stalled. If §3.1
  is too hard, ship §3.4 and §3.3 first as pure scaffolding upgrades.
- If T-II-2-009 Piece 9 stalls your §3.1, take it as a hypothesis in your
  intermediate theorems (witness form), then it becomes a downstream
  pickup once Piece 9 lands.
- The scaffold (`RouteA.lean`) is **load-bearing** — don't break it. Add
  new theorems beside it; preserve the existing ones.
- If you need to refactor `IsDualOf` to take E₁ → E₂ instead of E → E for
  full Silverman III.6.1 generality, **don't** — the Hasse-Weil application
  only needs the E → E case. Stay focused.

---

## 10. Done definition

When you commit your last patch, the following must hold:

```bash
$ grep -c sorry HasseWeil/DualIsogeny.lean
0
$ grep -c sorry HasseWeil/DegreeQuadraticForm.lean
0
$ lake build  # exits 0
$ lake env lean -c <(echo 'import HasseWeil.HasseBound
#print axioms HasseWeil.hasse_bound')
'HasseWeil.hasse_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

When `hasse_bound` is axiom-clean, **Hasse-Weil is closed**. Update the
ticket `T-HASSE-CLOSE-C-dual-existence.md` to DONE; bump INDEX.md
statistics; add a worker log entry.

Good luck.
