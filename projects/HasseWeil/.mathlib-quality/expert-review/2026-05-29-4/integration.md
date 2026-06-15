# Reply integration — round 10 (2026-05-29)

Reply: ./reply.md   Brief: ./brief.md

## Verdict (one line)
Leaf 1 via NARROW Route A: (1) minimal Wall A (rV−s≠0 ⟹ ord_O((rV−s)*x)<0, makes rV−s genuine);
(2) the genuine-isogeny EXTENSIONALITY lemma (pullback determined by geometric point-map) to
upgrade the shipped point-map composition (rV−s)(rπ−s)=[N] to the comorphism identity, ELIMINATING
Wall B; (3) Wall C (shipped). Route B (Weil-pairing) fallback only. No cheap Q3 third route.

## Interpretation
Decisive. Extensionality replaces Wall B but NOT Wall A (needs rV−s genuine first). Separability
correction: rπ−s (≠0) separable ⟺ p∤s (a_{rπ−s}=−s). No third route avoiding deg(rπ−s)=N.

## Changes applied
- MODIFIED GAP-QF-DEGQF ticket: added the "★ ROUND-10 CHOSEN PLAN" (narrow Route A, 3 steps) with
  the extensionality lemma `genuine_isogeny_ext_of_geometric_pointMap_eq` as the Wall-B killer,
  the minimal Wall A form, the separability correction (p∤s), the Q2/Q3 verdicts, Route B as fallback.

## Changes rejected
- (none)

## Open questions remaining
- (none) — reviewer gave a complete narrowed plan.

## Decision recorded + scoping notes
- Leaf 1 plan = narrow Route A (3 steps). Next: implement.
- Infra status: NO IsGenuine predicate or isogeny-extensionality lemma exists yet (the key new brick).
  The shipped point-map composition (genuine_dual_comp_toAddMonoidHom_eq_mulByInt, GapSpines:1309) +
  Wall C (signed_degree_of_genuine_dual_pair) are in place. genuineIsogSmulSubV (rV−s via addIsog,
  Genuine.lean) needs the minimal Wall A pole bound.
- PROMISING: the extensionality lemma may be PROVABLE from the Leaf-2 embeddings↔points machinery
  (algHom_ext_x_y_gen_omega, embToPointOmega): a genuine isogeny's pullback f↦f∘φ is determined by
  its action on x_gen,y_gen, which the point-map fixes via the embedding correspondence. The
  HasseWeil.EC.Isogeny / toCurveMap / CoordHom geometric type is available for "IsGenuine".
