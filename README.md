# Riemann Hypothesis — Hilbert–Pólya / Adelic Flow Formalization

This repository formalizes the current Number-II program in Lean 4.

## Formalized now

- Primitive multiplicative scales are exactly prime numbers.
- Repetition lengths satisfy `log(p^m) = m log p`.
- For prime `p`, the local p-adic return modulus satisfies
  `|p^m|_p = p^{-m}`.
- At every different prime `q != p`, `p^m` is a q-adic unit and contributes norm `1`.
- A `GlobalAdelicFlowSpec` records the exact remaining global obligations.

## Remaining global boundary

The current Lean development does **not** yet prove existence of the required global adelic flow or the complete Weil/Riemann explicit trace formula.

The next theorem-level goals are:

1. Construct a single global adelic flow realizing the local prime models simultaneously.
2. Prove its primitive closed arithmetic cycles are exactly those indexed by primes.
3. Derive the global return Jacobian from the adelic product structure.
4. Derive the complete trace formula, including the archimedean/Gamma contribution and signs.
5. Connect that trace formula to a self-adjoint Hilbert–Pólya operator.

## Build

```bash
lake update
lake build
```

The project targets Lean `v4.33.1` and mathlib `v4.33.1`.
