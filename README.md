# monogate-lean

Machine-verified proofs for the monogate EML operator framework.

These Lean 4 proofs verify lower bounds and upper bounds for the SuperBEST routing table,
establishing that no single F16 operator can compute certain elementary operations in fewer
nodes than claimed, and that explicit 1-node constructions exist on the positive domain.

## Verified Theorems (0 sorries) — 10 files

- **AddLowerBound.lean** — SB(add) ≥ 2: no single F16 operator computes x + y
- **SubLowerBound.lean** — SB(sub) ≥ 2: no single F16 operator computes x − y
- **MulLowerBound.lean** — SB(mul) ≥ 2: no single F16 operator computes x · y
- **DivLowerBound.lean** — SB(div) ≥ 2: no single F16 operator computes x / y
- **DivLowerBound3.lean** — Extended division lower bound (exp-type outer cases, 2-node positive construction)
- **UpperBounds.lean** — Positive-domain 1-node constructions: exp, mul, pow, recip, sqrt via F16 (`superbest_positive_one_node_ops`)
- **ModelAudit.lean** — SuperBEST v5.1 → v5.2 correction: sqrt = 1n not 2n, mul = 1n positive domain
- **EMLDepth.lean** — Complex EML depth hierarchy: Euler Gateway (`euler_gateway`), Euler Identity (`euler_identity`), EML-0 ⊊ EML-1 (`exp_not_constant`)
- **EMLDuality.lean** — exp-log multiplier duality at fixed points: for `z` in the slit plane with `Complex.exp z = z`, `deriv exp z * deriv log z = 1` (`exp_log_multiplier_product_at_fixed_point`). Every Lambert fixed point is therefore exp-repelling and log-attracting, with reciprocal multipliers.
- **HyperbolicPreservation.lean** — hyperbolic functions preserve ELC: `sinh`, `cosh`, `tanh` are explicit arithmetic combinations of `exp(±x)` and hence map ELC inputs to ELC outputs. Includes numerical witnesses `sinh(ln 2) = 3/4`, `cosh(ln 2) = 5/4`, and the 3-4-5 Pythagorean-triple identity at `ln 2`.

## Partial (2 sorries remaining) — 1 file

- **InfiniteZerosBarrier.lean** — T01 (Infinite Zeros Barrier). Parts A–C proved with 0 sorries: sin has infinitely many zeros on ℝ, analytic functions have finitely many zeros on compacts, and every well-formed EML tree is real-analytic on (0,∞) (including a full case-analysis closure for depth ≤ 1). Parts D has 2 open sorries (`sin_not_in_eml`, `sin_not_in_real_EML_k`) pending a quantitative zero-count bound for depth-k EML trees — a Khovanskii / Wilkie 1996 o-minimal-structure result not yet formalized in Mathlib.

## Build

Requires Lean 4 and Mathlib v4.14.0.

```bash
lake build
```

## Context

These proofs support the SuperBEST routing table documented at
[monogate.org](https://monogate.org). The F16 family of 16 exp-ln
binary operators is defined in Odrzywołek (2026), arXiv:2603.21852.

Monogate Research.
