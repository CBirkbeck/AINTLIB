# Reply integration — round 8 (2026-05-29)

Reply: ./reply.md   Brief: ./brief.md

## Verdict (one line)
Leaf 2 via BASE CHANGE to K̄=F̄_q + the separable-isogeny fibre count (Silverman III.4.10a) there; descend the degree; identify the fibre with E(F_q) by the fixed-field lemma a^q=a ⟺ a∈F_q. Avoid the K-level residue-degree (f_P=1) statement.

## Interpretation
One decisive recommendation. Round-7 "Option B" (separable ⇒ e_P=1) was applied to the wrong morphism (the degree-2 composite x∘(1−π), where kernel places have e=2). The correct mechanism counts the GEOMETRIC fibre over K̄ (residue degrees vanish): deg(1−π)=deg((1−π)_K̄)=#ker((1−π)_K̄)=#E(F_q).

## Changes applied
- MODIFIED `separable-isogeny-fibre-count` ticket: replaced the (wrong) round-7 Option-B e_P=1 sketch with the round-8 base-change route + the 4 sub-lemmas + the key fixed-field lemma; marked the K-level closed-point/Frobenius-orbit dictionary as the deprioritized alternative; recorded the infra to build (concrete Isogeny.baseChange + degree invariance; separability under base change; the alg-closed #ker=sepDegree fibre count = III.4.10a core, NOT yet in project/mathlib; the fixed-field equivalence, mostly mathlib).
- Kept the shipped `pointCount ≤ deg(1−π)` as a sanity check.

## Changes rejected
- (none)

## Open questions remaining
- (none unanswered) — the reviewer gave a complete, decisive plan.

## Decision recorded
- Base-change route is the chosen Leaf-2 path. Next: implement the 4 lemmas (pending user go-ahead).
- Note: the alg-closed fibre count (#ker = sepDegree for a separable isogeny over K̄, III.4.10a) is the substantive new piece; the fixed-field lemma is near-mathlib.
