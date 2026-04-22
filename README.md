# monogate-lean

Machine-verified proofs for the monogate EML operator framework.

These Lean 4 proofs verify lower bounds and upper bounds for the SuperBEST routing table,
establishing that no single F16 operator can compute certain elementary operations in fewer
nodes than claimed, and that explicit 1-node constructions exist on the positive domain.

## Verified Theorems (0 sorries)

- **AddLowerBound.lean** — SB(add) ≥ 2: no single F16 operator computes x + y
- **SubLowerBound.lean** — SB(sub) ≥ 2: no single F16 operator computes x − y
- **MulLowerBound.lean** — SB(mul) ≥ 2: no single F16 operator computes x · y
- **DivLowerBound.lean** — SB(div) ≥ 2: no single F16 operator computes x / y
- **DivLowerBound3.lean** — Extended division lower bound (exp-type outer cases, 2-node positive construction)
- **UpperBounds.lean** — Positive-domain 1-node constructions: exp, mul, pow, recip, sqrt via F16 (`superbest_positive_one_node_ops`)
- **ModelAudit.lean** — SuperBEST v5.1 → v5.2 correction: sqrt = 1n not 2n, mul = 1n positive domain
- **NegLowerBound.lean** — SB(neg) ≥ 2: no single F16 operator with any constant computes −x (`SB_neg_ge_two`)
- **EMLDepth.lean** — Complex EML depth hierarchy: Euler Gateway (`euler_gateway`), Euler Identity (`euler_identity`), EML-0 ⊊ EML-1 (`exp_not_constant`)

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
