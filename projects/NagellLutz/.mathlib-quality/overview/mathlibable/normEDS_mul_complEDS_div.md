# Mathlibable assessment: `normEDS_mul_complEDS_div`

**Verdict: YES-but-generalise-first**

(Upstream it *together with its parent* `normEDS_mul_complEDS` — the corollary is too thin to PR alone, but the product-identity API it caps is genuine mathlib content that fills a standing mathlib TODO.)

---

## 1. The declaration

- **Qualified name:** `normEDS_mul_complEDS_div` (no namespace prefix — it sits at file top level, *before* the next `namespace EllSequence` at L1356; verified it is *not* inside any namespace).
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1349` (re-verified 2026-06-21).

```lean
omit ellW ellU one two dvd₁₂ dvd₁₃ dvd₂₄ h₁ h₂ in
lemma normEDS_mul_complEDS_div {m : ℤ} (n : ℤ) (dvd : m ∣ n) :
    normEDS b c d m * complEDS b c d m (n / m) = normEDS b c d n := by
  rcases eq_or_ne m 0 with rfl | hm
  · obtain ⟨n, rfl⟩ := dvd; simp
  · obtain ⟨n, rfl⟩ := dvd
    rw [Int.mul_ediv_cancel_left _ hm, normEDS_mul_complEDS, mul_comm]
```

(Note: the source has since been edited — the `m = 0` case is now handled internally via
`eq_or_ne`, so the explicit `(hm : m ≠ 0)` hypothesis of the earlier version is gone; the
statement now holds unconditionally given `m ∣ n`. Verdict and reasoning below are unchanged.)

Here `b c d : R` for a `CommRing R`, `normEDS b c d : ℤ → R` is the canonical normalised
elliptic divisibility sequence, and `complEDS b c d m n` is the complement sequence
(`= normEDS b c d (n·m) / normEDS b c d m`, made total).

**Mathematical content.** For a divisor `m | n`, the `m`-th term of the EDS
times the complement evaluated at the quotient `n/m` reconstructs the `n`-th term:
`W(m) · Wᶜ(m, n/m) = W(n)`. It is the divisor-indexed restatement of the product identity
`normEDS_mul_complEDS (m n) : W(m) · Wᶜ(m, n) = W(n·m)` — exactly the witness that `W(m) ∣ W(n)`.

## 2. Literature search

- EDS divisibility is the Ward (1948) *Memoir on Elliptic Divisibility Sequences* property:
  a divisibility sequence satisfies `W(m) ∣ W(n)` whenever `m ∣ n`; for an EDS this is classical.
  The "complement sequence" `Wᶜ` (the explicit cofactor `W(nm)/W(m)`) is the constructive
  witness of that divisibility. References: Wikipedia "Elliptic divisibility sequence";
  Ward's memoir; Stange "Elliptic nets and elliptic curves" (arXiv:0710.1316);
  Silverman et al. on division-polynomial valuations (arXiv:1108.3051).
- The lemma itself is a *bookkeeping reindex* of the divisibility witness; it is not a named
  theorem in the literature, just the natural API form of "`m | n ⇒ W(m) | W(n)` with an
  explicit cofactor".

## 3. Mathlib search (five methods; mathlib pinned at `09b373db6e24`, v4.32.0-rc1)

Searched `.lake/packages/mathlib/` directly (the index/loogle is the same content). Re-verified at
the current pin on 2026-06-21; findings unchanged from the earlier pin.

- **`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` already contains** `normEDS`,
  `complEDS₂`, `complEDS'`, **`complEDS`** (def at L427: `n.sign * complEDS' b c d k n.natAbs`),
  `normEDS_mul_complEDS₂`, `normEDS_dvd_normEDS_two_mul`, the `complEDS_even/_odd` recursion
  laws, and recursion principles (L475/L488), plus `map_complEDS`. **The mathlib file ends at
  L544 (`map_complEDS`); total 547 lines.**
- **Mathlib does NOT prove the general product identity.** There is no
  `normEDS_mul_complEDS` and no `normEDS_mul_complEDS_div` anywhere in mathlib. The only
  `*_mul_compl*` lemma is `normEDS_mul_complEDS₂` (the `n = 2` case). `grep -rn` across all of
  `Mathlib/` for `normEDS_mul_complEDS\b` / `mul_compl_eq_apply_mul` / `complEDS_div` returns
  nothing beyond the `₂` variant.
- **Mathlib has an explicit open TODO for precisely this** (file header L44–L45):
  - "TODO: prove that `normEDS` satisfies `IsEllDivSequence`."
  - "TODO: prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`."
  Mathlib defines `IsDivSequence`/`IsEllDivSequence` (L87–L92) but never proves `normEDS` is one
  — the product identity `normEDS_mul_complEDS` (this lemma's parent) is exactly the missing
  ingredient (`W(m) · Wᶜ = W(nm) ⇒ W(m) ∣ W(nm) ⇒ IsDivSequence (normEDS …)`).

**Conclusion of search:** mathlib hosts the *definition* `complEDS` this builds on, but neither
this lemma nor its load-bearing parent exists upstream.

### Note: signature divergence (project fork vs. mathlib)

The project did **not** copy mathlib's `complEDS` verbatim. Mathlib's `complEDS b c d k n` is
built directly on `normEDS`. The project's `EllSequence.complEDS b c d m n` (L1111) is
`compl (normEDS b c d) (compl₂EDS b c d) m n` — a *generic* `EllSequence.compl W₁ compl₂ m n`
over an abstract sequence, with the product identity first proved abstractly as
`IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` (L1293) for any elliptic sequence
whose terms are non-zero-divisors, then specialised to `normEDS`. So the project both
**re-architects** mathlib's complement API (more general base) **and adds** the product theorem
mathlib lacks.

## 4. Generality analysis

- Stated over an arbitrary `CommRing R` with parameters `b c d : R`. That is already the
  maximal natural generality for the `normEDS` construction (no integral-domain / field
  hypothesis needed). Good.
- Hypotheses are minimal: just `m ∣ n` (the `m = 0` sub-case is dispatched internally via
  `eq_or_ne`; no `m ≠ 0` hypothesis is exposed). No weakening available.
- It is strictly *less* general than its parent `normEDS_mul_complEDS (m n : ℤ)` (which needs no
  divisibility hypothesis at all). The `_div` form is a convenience reindex, not a generalisation.

## 5. Composition check (can ≤3 mathlib calls give it?)

The proof is a case split on `m = 0` plus, in the main branch, two rewrites:
`rw [Int.mul_ediv_cancel_left _ hm, normEDS_mul_complEDS, mul_comm]`.

- `Int.mul_ediv_cancel_left` — **in mathlib** (`Mathlib/Data/Int/Init.lean`; used e.g. in
  `PythagoreanTriples.lean`). `mul_comm`, `eq_or_ne` — in mathlib.
- `normEDS_mul_complEDS` — **NOT in mathlib.** This is the essential middle step and carries all
  the content.

Therefore the lemma is **not** composable from current mathlib in ≤3 calls: one of the three
calls is to a lemma (`normEDS_mul_complEDS`) that does not exist upstream. Rules out
`NO-composable-from-mathlib`. (Once the parent is upstreamed, the corollary *does* become a
≤3-call composition — which is exactly why it should travel *with* the parent, not alone.)

## 6. Cross-repo duplication (consolidation signal)

A near-identical lemma also lives in
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:809`, consumed there
at L889/L892/L895 (the HasseWeil twin still carries the older `(hm : m ≠ 0)` signature; the
NagellLutz copy has since dropped it). So `normEDS_mul_complEDS_div` (and its parent
`normEDS_mul_complEDS`) is duplicated across NagellLutz and HasseWeil. This is a same-monorepo
dedup target *and* an upstream candidate: two independent NT developments both needed it, which
corroborates that it is real, reusable EDS API rather than a one-off.

## 7. Verdict and rationale

**YES-but-generalise-first.**

- It is **not** in mathlib (`NO-mathlib-has-it` rejected) and **not** composable from current
  mathlib because its parent `normEDS_mul_complEDS` is absent (`NO-composable-from-mathlib`
  rejected).
- It is genuine, correctly-general, reusable content that **fills mathlib's own stated TODO**
  (proving `normEDS` is an `IsEllDivSequence`), builds on the `complEDS` definition mathlib
  already ships, and is duplicated across two projects.
- Not `YES-add-as-is` because, *in isolation*, this decl is a one-line reindex whose entire
  value is contingent on the un-upstreamed parent `normEDS_mul_complEDS` (and the abstract
  `EllSequence.compl` + `IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` it rests
  on). The right upstreaming unit is the **product-identity sub-API as a bundle**
  (`mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` → `normEDS_mul_complEDS` →
  `normEDS_mul_complEDS_div`, then `normEDS_dvd_normEDS_mul` / `isDivSequence_normEDS`), landing
  in the existing `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` right after the
  current `complEDS` block. PR the parent + corollary together (and reconcile the project's
  generalised `compl` base against mathlib's direct `complEDS`); do not submit this corollary
  standalone.

**Suggested mathlib home:** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (the
`ComplEDS` section), closing out the file's L44 TODO.
