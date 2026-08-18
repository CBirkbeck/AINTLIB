# Mathlibable assessment — `WeierstrassCurve.Universal.Affine.smulX_sub_sub_smulX_add`

**Verdict: NO-composable-from-mathlib**

(Adjacent considerations: NOT in mathlib as-is, and currently NOT even *statable* in mathlib —
its subject `smulX` is a project-local definition. Within the NagellLutz project it is a trivial
2-line corollary of its sibling `smulX_sub_smulX`.)

---

## 1. The declaration (verified from source)

File: `projects/NagellLutz/LutzNagell/ZSMul.lean:196`
Namespaces: `WeierstrassCurve` → `Universal` → `Affine`, so the true qualified name is

```
WeierstrassCurve.Universal.Affine.smulX_sub_sub_smulX_add
```

(The parsed name in the ticket was correct.)

```lean
lemma smulX_sub_sub_smulX_add (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulX (n - m) - smulX (n + m) = (ψᵤ (2 * n) * ψᵤ (2 * m)) / (ψᵤ (n + m) * ψᵤ (n - m)) ^ 2 := by
  rw [smulX_sub_smulX sub_ne add_ne]
  simp only [show n + m + (n - m) = 2 * n from by ring, show n + m - (n - m) = 2 * m from by ring]
```

### What the symbols mean (all project-local, none in mathlib)
- `Universal.Field` — the fraction field of the *universal* Weierstrass curve's coordinate ring
  `ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨P⟩`. Defined in `projects/NagellLutz/LutzNagell/Universal.lean`.
- `ψᵤ n := polyToField (curve.ψ n)` — the n-th division polynomial of the universal curve, pushed
  into `Universal.Field` (`ZSMul.lean:132`).
- `smulX n := polyToField (curve.φ n) / (ψᵤ n) ^ 2` — the rational function `φₙ/ψₙ²`, i.e. the
  X-coordinate of `n • (X,Y)` on the universal curve (`ZSMul.lean:164`).

### Mathematical content
For the universal point `P = (X,Y)`, with `x(kP) = φₖ/ψₖ²`, this states
`x((n−m)P) − x((n+m)P) = ψ_{2n} ψ_{2m} / (ψ_{n+m} ψ_{n−m})²`.
It is the `k = n−m`, `k' = n+m` re-indexing of the standard EDS X-coordinate-difference identity
`x(aP) − x(bP) = ψ_{a+b} ψ_{a−b} / (ψ_a ψ_b)²`. Used once, at `ZSMul.lean:315`, as a single rewrite
inside `smulX_add`, which feeds the affine multiplication-by-n formula
`Universal.Affine.zsmul_point_eq_smulX_smulY`.

---

## 2. Literature search

- **Wikipedia, "Division polynomials" / "Elliptic divisibility sequence"**, and the standard
  references (Silverman *AEC* Ex. 3.7; Stange, *The Tangent and Secant…*; Ayad). These give the
  X-coordinate formula `x(nP) = φₙ/ψₙ²` and difference/addition identities of exactly this Somos-/
  EDS-quartic shape. The specialization here (`a = n−m`, `b = n+m`, using `(n+m)±(n−m) = 2n, 2m`)
  is a routine re-indexing, **not** a separately-named theorem.
- Search via WebSearch confirmed these are the relevant sources; none names a `smulX (n−m) − smulX (n+m)` identity — it is an internal computational step on the way to the multiplication formula.

This is a *helper* on the path to a named theorem (multiplication-by-n in terms of division
polynomials), not a target theorem in its own right.

## 3. Mathlib search (five methods)

- **Name / grep.** `def smulX`, `smulX_sub_sub_smulX_add`, `polyToField`, and `namespace Universal`
  return **0 hits** in `.lake/packages/mathlib/`. (The only `Universal*` namespaces in mathlib are
  `UniversallyOpen` and `UniversalEnvelopingAlgebra` — unrelated.)
- **DivisionPolynomial/Basic.lean.** Defines `ψ₂, Ψ₂Sq, Ψ₃, preΨ₄, preΨ', preΨ, ψ, φ, ω, ΨSq` over a
  *general* `WeierstrassCurve R` — but has **no universal curve, no `polyToField`, no `smulX`, and no
  "X-coordinate of n•P" rational function**. So the very *subject* of this lemma does not exist in
  mathlib.
- **EllipticDivisibilitySequence.lean.** Has `IsEllSequence`, `IsDivSequence`, `normEDS` and its
  recurrences (`normEDS_even`, `normEDS_odd`, …), but **no `net` / Somos-quartic four-term identity
  API**. The `EllSequence.net` machinery this track relies on is itself **project-local**
  (`NagellLutz/.../EllipticDivisibilitySequence.lean:115`, duplicated in HasseWeil) — also not in
  mathlib.
- **loogle / leansearch (mathlib index).** No statement of the form
  `x((n−m)P) − x((n+m)P) = …` exists; mathlib has no `smulX`-type object to phrase it against.

**Conclusion:** mathlib does **not** contain this lemma, nor any more general form of it, nor the
vocabulary (`smulX`) needed to state it.

## 4. Generality analysis

The literature-standard form is the two-index identity
`x(aP) − x(bP) = ψ_{a+b} ψ_{a−b} / (ψ_a ψ_b)²` — which in this project is exactly the **sibling**
lemma `smulX_sub_smulX` (`ZSMul.lean:186`). The lemma under review is a strictly *less* general,
re-indexed special case (`a := n−m`, `b := n+m`). So it is the opposite of "needs generalising":
its own more-general form already exists next to it and is the one doing the real work. No mathlib-
ward generalisation is warranted; only the *general* `smulX`/division-polynomial-coordinate API
(not this corollary) could conceivably be mathlib-bound, and that is a much larger upstreaming
question about the whole `Universal` apparatus, well outside one declaration.

## 5. Composition check (≤ 3 mathlib/project calls?)

**Yes, decisively.** The full proof is two steps:
1. `rw [smulX_sub_smulX sub_ne add_ne]` — apply the general sibling identity (the substantive lemma,
   which itself invokes the EDS three-term relation `isEllSequence_ψᵤ`);
2. `simp only [(n+m)+(n−m) = 2n, (n+m)−(n−m) = 2m]` — two `ring`-proved index rewrites.

Given `smulX_sub_smulX`, this lemma is recovered in a single rewrite plus `ring`-normalization of the
indices. It is a textbook "composable in ≤ 3 calls" corollary. (And the composition is *of project
API*, not mathlib API — because mathlib lacks the subject entirely.)

## 6. Duplication note (project-internal, for the cleaner)

The identical lemma — same statement, same 2-line proof — also lives at
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:277`, together with the whole
`Universal` / `ψᵤ` / `smulX` / `EllSequence.net` track (verbatim duplicate of NagellLutz). This is a
**cross-project dedup** target for the on-`main` cleanup fleet: the shared universal-division-
polynomial development belongs in `Common/`, not copied per project. That is independent of
mathlib-ability and does not change the verdict.

---

## Verdict

**NO-composable-from-mathlib.** Not present in mathlib and not statable there (subject `smulX` is
project-local); within the project it is a trivial ≤3-call corollary of the more general
`smulX_sub_smulX`. Keep it where it is as a private helper for the multiplication-by-n formula.
The mathlib-relevant action, if any, concerns upstreaming the *general* universal-curve division-
polynomial-coordinate API — a separate, larger question — not this corollary. Cross-project
duplication with HasseWeil is a cleanup-fleet dedup item, not a mathlib item.
