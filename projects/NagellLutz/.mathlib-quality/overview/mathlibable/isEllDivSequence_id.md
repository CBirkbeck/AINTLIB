# Mathlibable assessment — `isEllDivSequence_id`

**Verdict: NO-mathlib-has-it**

## Declaration

- **Qualified name:** `isEllDivSequence_id` (top-level; no enclosing namespace)
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:616`
- **Statement (project):**
  ```lean
  /-- The identity sequence is an EDS. -/
  theorem isEllDivSequence_id : IsEllDivSequence id :=
    ⟨isEllSequence_id, isDivSequence_id⟩
  ```
  where (same file)
  ```lean
  def IsEllDivSequence : Prop := IsEllSequence W ∧ IsDivSequence W
  lemma isEllSequence_id : IsEllSequence id := fun _ _ _ ↦ by simp only [Rel₃, id_eq]; ring1
  lemma isDivSequence_id : IsDivSequence id  := fun _ _ ↦ id
  ```

The result says the identity sequence `id : ℤ → ℤ` (`n ↦ n`) is an elliptic divisibility
sequence: it satisfies the elliptic-sequence functional equation
`W(m+n)W(m−n)W(r)² = W(m+r)W(m−r)W(n)² − W(n+r)W(n−r)W(m)²` (here a polynomial identity in
`m,n,r`, closed by `ring`), and it is a divisibility sequence (`m ∣ n → m ∣ n`, trivially `id`).

## Project context

This file is an explicit **fork** of mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`
(same header, same author: David Kurniadi Angdinata, Apache-2.0). The NagellLutz project vendors and
extends the EDS / division-polynomial API; this particular declaration is part of the upstream
boilerplate that was carried along, not new mathematics.

## Mathlib search (five methods)

Searched the pinned mathlib (`rev = d90090f647ca`, lean `v4.31.0-rc2`) at
`.lake/packages/mathlib`.

1. **Exact-name grep** — `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:101` contains
   ```lean
   /-- The identity sequence is an EDS. -/
   theorem isEllDivSequence_id : IsEllDivSequence id :=
     ⟨isEllSequence_id, isDivSequence_id⟩
   ```
   — **byte-for-byte the same theorem, the same name, the same proof.** Its two helper lemmas
   `isEllSequence_id` (line 94) and `isDivSequence_id` (line 97) are also present upstream.
2. **Definition check** — `IsEllSequence`, `IsDivSequence`, `IsEllDivSequence` are all defined
   upstream (lines 82–92) with the identical elliptic functional equation.
3. **Leansearch / Loogle (mathlib index)** — not needed; located by direct source grep, which is
   authoritative for "already in mathlib".
4. **Consumers** — upstream `isEllDivSequence_id` sits in the same `section IsEllDivSequence`
   alongside `IsEllDivSequence.smul` / `.map`, exactly mirroring the project file.
5. **Generality** — the only divergence is in the *definition* `IsDivSequence`: mathlib uses
   `∀ m n : ℕ, m ∣ n → W m ∣ W n` (ℕ-indexed), whereas the fork rewrote it to
   `∀ m n : ℤ, m ∣ n → W m ∣ W n` (ℤ-indexed). This is a property of the **definition the project
   forked**, not of `isEllDivSequence_id` itself; the theorem, its name, and its trivial pairing
   proof are unchanged. If the ℤ-indexed `IsDivSequence` were ever judged the better definition,
   that is a generalisation question for `IsDivSequence` (and its `isDivSequence_id`), not grounds
   to add `isEllDivSequence_id` — mathlib already has the named result.

## Literature

`IsEllDivSequence id` is the most elementary example of an EDS (Ward, *Memoir on Elliptic
Divisibility Sequences*, 1948 — cited in the mathlib file's references). It is a standard
warm-up/sanity example, fully formalised upstream already. No literature sweep can change a verdict
where the declaration is verbatim present in mathlib.

## Composition check

Moot — the declaration *is* mathlib's `isEllDivSequence_id`. (For completeness it is itself a
1-call composition: `⟨isEllSequence_id, isDivSequence_id⟩`, two upstream one-liners.)

## Conclusion

`isEllDivSequence_id` already exists in mathlib with the identical name, statement, and proof
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:101`). The project copy is a vendored fork
of that exact file. Nothing to upstream.

**Bucket: NO-mathlib-has-it** — `isEllDivSequence_id` is verbatim in
`Mathlib.NumberTheory.EllipticDivisibilitySequence`; the project file forks that very file.
