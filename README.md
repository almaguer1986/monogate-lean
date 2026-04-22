# monogate-lean

Machine-verified proofs for the monogate EML operator framework.

These Lean 4 proofs verify lower bounds for the SuperBEST routing table,
establishing that no single F16 operator can compute certain elementary
operations in fewer nodes than claimed.

## Verified Theorems (0 sorries)

- **AddLowerBound.lean** — SB(add) ≥ 2: no single F16 operator computes x + y
- **DivLowerBound.lean** — SB(div) ≥ 2: no single F16 operator computes x / y
- **DivLowerBound3.lean** — Extended division lower bound

## Build

Requires Lean 4 and Mathlib v4.14.0.

```bash
lake build
```

## Context

These proofs support the SuperBEST routing table documented at
[monogate.org](https://monogate.org). The F16 family of 16 exp-ln
binary operators is defined in Odrzywołek (2026), arXiv:2603.21852.

Research by Arturo R. Almaguer.
