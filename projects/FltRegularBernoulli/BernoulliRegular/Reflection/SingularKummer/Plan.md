# Singular Kummer Lift

This directory contains the singular-Kummer part of the component-reflection
route.  Its goal is not yet to prove reflection.  It is only to pass from a
nonzero component of the elementary class-group quotient to a singular Kummer
class with the same character.

## Mathematical Goal

Let `p` be an odd prime, let `K = Q(zeta_p)`, let
`Delta = Gal(K / Q)`, let `A` be the `p`-Sylow subgroup of the class group of
`K`, and let

```text
V = A / A^p.
```

For an even character index `i`, assume

```text
V_i != 0.
```

This stage should produce a class `s` in the singular group

```text
S = { alpha in K^x : (alpha) = b^p for some fractional ideal b } / (K^x)^p
```

such that:

```text
s lies in S_i,
s maps to a nonzero class in A[p]_i.
```

Equivalently, after choosing a representative `alpha in K^x`, we have

```text
(alpha) = b^p
```

for some fractional ideal `b`, the class of `b` is nonzero in `A[p]_i`, and
the class of `alpha` in `K^x / (K^x)^p` has the same `Delta`-character `i`.

## Proof Strategy

1. Prove the finite `p`-group comparison needed to translate the hypothesis on
   `V = A / A^p` into a statement about `A[p]`.

   For a finite abelian `p`-group with a `Delta`-action, the elementary quotient
   `A / A^p` and the subgroup `A[p]` have the same nonzero character support.
   This uses the finite filtration by powers of `p` and semisimplicity of
   `F_p[Delta]`, since `|Delta| = p - 1` is prime to `p`.

2. Define the singular group `S`.

   An element of `S` is represented by an element `alpha in K^x` whose principal
   ideal is a `p`-th power of a fractional ideal.  The quotient is taken modulo
   global `p`-th powers.

3. Define the natural map

   ```text
   S -> A[p]
   ```

   by sending the class of `alpha`, with `(alpha) = b^p`, to the class of `b`.
   This must be checked to be well-defined:

   - changing `b` changes it only by a principal ideal,
   - changing `alpha` by a global `p`-th power changes `b` only by a principal
     ideal,
   - the resulting class is killed by `p`.

4. Prove surjectivity of `S -> A[p]`.

   If a class `[b]` lies in `A[p]`, then `b^p` is principal, say
   `b^p = (alpha)`.  Then `alpha` defines a singular class mapping to `[b]`.

5. Identify the kernel.

   The kernel consists exactly of global unit classes:

   ```text
   E / E^p -> S.
   ```

   Indeed, if the ideal class of `b` is trivial, write `b = (gamma)`.  Then
   `(alpha) = (gamma)^p`, so `alpha = u gamma^p` for a global unit `u`.

6. Record the exact sequence of `F_p[Delta]`-modules:

   ```text
   E / E^p -> S -> A[p] -> 0.
   ```

   The maps must be `Delta`-equivariant.

7. Pass to the `i`-th character component.

   Since `p` does not divide `|Delta|`, taking the `i`-th component is exact.
   Hence

   ```text
   (E / E^p)_i -> S_i -> A[p]_i -> 0
   ```

   is exact.

8. Choose the desired singular class.

   From `V_i != 0`, the finite-group comparison gives `A[p]_i != 0`.  By
   surjectivity on the
   `i`-component, choose `s in S_i` mapping to a nonzero class of `A[p]_i`.

## Deliberate Boundary

This singular-Kummer lift does not prove local primarity, unramifiedness at the
prime above `p`, residue-symbol reciprocity, Chebotarev nonvanishing, or
reflection itself.  Those belong to later arguments.
