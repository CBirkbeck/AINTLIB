# Reviewer reply — round 4 (2026-05-27)

## Short verdict

Use **Route B: base-change to K̄, then descend.** Given the algebraically closed fibre-count theorem
is already proved, Route B has the shortest remaining path. Route C (intrinsic Galois/translation) is
true but proving it cleanly in Lean reintroduces the same hard theorem (`#ker φ = deg φ`, or the
quotient `E/ker γ`, or the finite étale torsor statement). Route A stays abandoned — over F_q a prime
over (1/f) may correspond to a closed point of residue degree > 1, so it bottoms out in the same
geometric-kernel issue. The §5 integration hazard is real: do NOT combine "algebraically closed base"
and "finite point set" in one hypothesis package; separate alg-closed fibre count from finite-field
point count by an explicit descent step.

## Q1 — Route B or C?

Choose **Route B**. Its only two remaining pieces: (1) construct/base-change the genuine (1−π) and
identify it with 1−Frob_q on E_{K̄}; (2) prove the fixed locus of q-Frobenius on E(K̄) is exactly
E(F_q). Both concrete and elementary vs Route C. Route C's statement (`K(E)/(1−π)*K(E)` Galois with
group = translation by ker(1−π)) needs `#ker φ = deg φ`, or `φ: E→E/G` a quotient, or finite étale
G-torsor — exactly the deep facts being avoided. The easy inclusion `ker φ ↪ Aut(K(E)/φ*K(E'))` does
not prove surjectivity; the missing inequality is again a degree/cardinality statement. Route C is good
long-term III.4 infrastructure, not the fastest route here.

## Q2 — Cleanest formulation of the descent E(K̄)^{Frob_q} = E(F_q)

Do it by **coordinate fixed points, not Lang's theorem.** Prove the field lemma:
`a^q = a ⟺ a ∈ im(K → K̄)`. Clean proof: X^q − X has exactly the q elements of K as roots; over K̄ it
has at most q roots and derivative −1 in char p, so no repeated roots; therefore its K̄-roots are
exactly the embedded copy of K. Then for points: O is fixed; for affine P=(x,y) ∈ E(K̄),
Frob_q(P)=P iff x^q=x ∧ y^q=y iff x,y ∈ K iff P ∈ E(K). Much smaller than Lang's theorem (overkill —
you need only the kernel/fixed-locus computation, not surjectivity of 1−Frob).

Lean targets:
```
theorem frobenius_fixed_iff_mem_baseField (a : AlgebraicClosure K) :
    a ^ Fintype.card K = a ↔ ∃ b : K, algebraMap K (AlgebraicClosure K) b = a
theorem point_fixed_by_frobenius_iff_base_point
    (P : (W.baseChange (AlgebraicClosure K)).Point) :
    frobenius_q_point P = P ↔ ∃ P0 : W.Point, includePoint P0 = P
theorem card_kernel_one_sub_frobenius_baseChange :
    Fintype.card (kernel (1 - frobenius_q) on E(Kbar)) = Fintype.card W.Point
```

## Q3 — Route C Galois/translation theorem

Correct in standard AG: for a separable isogeny φ:E→E', translations by ker φ identify the kernel with
Gal(K(E)/φ*K(E')). But not a free field-theory theorem. The inclusion `ker φ → Aut(K(E)/φ*K(E'))` is
straightforward; the hard part is surjectivity/cardinality `|ker φ| = [K(E):φ*K(E')]` — exactly
Silverman III.4.10(c), or via finite étale fibre / quotient E/ker φ. No tame/wild issues for 1−π once
separable; the real hidden hypothesis is that the kernel action is the FULL deck group (= the isogeny
is a quotient by its kernel). Yes Route C is the correct standard theorem; no it is not the cleanest
immediate path unless you already have finite étale torsors or quotient curves; clean citation
Silverman III.4.10(b/c) — but formalising it likely costs more than the remaining Route B descent.

## Q4 — Architecture sanity

Yes. Split alg-closure fibre count from finite-field point count. Correct Route B chain:
`deg(1−π) = deg((1−π)_K̄) = #ker((1−π)_K̄) = #E(F_q)`, with three distinct obligations: (1) degree
base-change invariance; (2) alg-closed fibre count for separable maps; (3) Frobenius fixed-locus
descent. Do NOT hide (3) as a hypothesis in the same theorem that assumes an alg-closed base. Correct
Route C chain `deg(1−π) = #ker(1−π) = #E(F_q)` — but the first equality IS the entire kernel-degree
theorem. Do not revive Route A: the Sinf/ramification prime count over a nonclosed field counts closed
points with residue degrees; concluding it counts exactly F_q-rational kernel points needs the same
geometric fixed-point/fibre fact.

## Recommended implementation plan

- **Step 1** — field fixed-subfield lemma `fixed_by_card_frobenius_iff_mem_range` (elementary
  polynomial-root counting on X^q − X).
- **Step 2** — point fixed-locus descent `baseChange_frobenius_fixed_iff` (cases P=O and affine (x,y)).
- **Step 3** — base-change of γ=1−π: `(1−π)_K̄ = 1 − Frob_q` on the base-changed curve (the current
  gap; keep separate from fixed-locus descent; prove point-map + pullback compatibility if isogeny
  equality is too strong).
- **Step 4** — compose with the already-proved alg-closed fibre count `#ker((1−π)_K̄) = deg((1−π)_K̄)`.

## Caution on the brief's wording

"#ker = deg" is precisely the theorem being formalised unless already over K̄ invoking the proved
alg-closed fibre count. Safe statement: "Over K̄, the proved separable fibre theorem gives
`#ker((1−π)_K̄) = deg((1−π)_K̄)`. The remaining finite-field step is identifying that kernel with E(F_q)."

## Bottom line

Use Route B. The fixed-locus descent is elementary and cheaper than the intrinsic Galois/translation
theorem (whose surjectivity is essentially the kernel-degree theorem). Route A not revived. Next best
target: the coordinate lemma `a^q = a ⟺ a ∈ F_q` in K̄, then the point-level fixed-locus equivalence.
