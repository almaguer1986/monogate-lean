# monogate-lean

Lean 4 formalization of the EML (Elementary Modulo Logarithms) operator
framework — barrier theorems, F16 lower bounds, hyperbolic-ELC
preservation, exp-log multiplier duality, and the open
chain-order / infinite-zeros conjectures.

## Overview

This project formalizes the operator-theoretic framework underlying
Monogate's SuperBEST routing system. The framework studies which
elementary functions are computable in `n` nodes of the F16 binary
operator family — a small alphabet of exp/log compositions over
`ℝ` — and proves separation theorems against richer target
functions (`+`, `−`, `×`, `÷`, `sin`).

* **Reference:** Odrzywołek (2026), [arXiv:2603.21852](https://arxiv.org/abs/2603.21852).
* **Companion site:** [monogate.org](https://monogate.org).
* **EML compiler:** the Forge stack lowers EML expressions through
  this verified operator algebra to C, Rust, Lean, Verilog, VHDL,
  Chisel, LLVM IR, and WebAssembly with cross-target equivalence.

## Status

* **18 submodules** under `MonogateEML/`, plus a top-level
  `MonogateEML.lean` aggregator that imports them all so
  `lake build` verifies the entire corpus in one pass.
* **16 files: 0 sorries.** Production-grade verified content.
* **2 files: 5 open sorries** at known Mathlib gaps (Khovanskii
  zero-count, o-minimal `ℝ_exp`). See **Open problems** below.
  The fifth sorry (`tower_base_eq_chain_order`) is a corollary of
  `chain_order_additivity` — formally still open until the parent
  conjecture is closed.

## Build

Requires Lean 4 (`leanprover/lean4:v4.14.0`) and Mathlib v4.14.0.
The pinned versions live in `lean-toolchain` and `lake-manifest.json`.

```bash
lake build
```

A clean build prints `Build completed successfully` plus exactly
five `declaration uses 'sorry'` warnings — one per open problem
listed below. No `error` lines.

## Dependencies

The project depends only on Mathlib. The key Mathlib modules used:

* `Mathlib.Analysis.SpecialFunctions.{Exp, Log, Pow}` — the F16
  operator family and the EML evaluation semantics.
* `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` — for
  `Real.sin`, `Real.sin_int_mul_pi`, the Infinite Zeros Barrier.
* `Mathlib.Analysis.Analytic.{Basic, IsolatedZeros}` — analytic
  continuation argument in `analytic_finite_zeros_compact`.
* `Mathlib.Data.Set.{Finite.Basic, Function}` — for
  `Set.infinite_of_injective_forall_mem`.
* `Mathlib.Topology.Algebra.Order.Compact` — Bolzano-Weierstrass
  in the Part B compactness argument.

## Main results

### Barrier theorems (operator-family lower bounds)

* `AddLowerBound.lean::SB_add_ge_two` — no single F16 operator
  computes `x + y`, hence `SB(add) ≥ 2`.
* `SubLowerBound.lean::SB_sub_ge_two` — same for `x − y`.
* `MulLowerBound.lean::SB_mul_ge_two` — same for `x · y` (over
  general reals; positive-domain bound is 1, see UpperBounds).
* `DivLowerBound.lean::SB_div_ge_two` — same for `x / y`.
* `DivLowerBound3.lean` — extended division barrier covering the
  exp-type outer cases plus a 2-node positive construction.

### Upper-bound constructions (1-node positive domain)

`UpperBounds.lean::superbest_positive_one_node_ops` — explicit
F16 constructions for `exp`, `mul`, `pow`, `recip`, `sqrt` on
`ℝ_>0`, each in a single F16 node. Each construction is verified
by a `_one_node_positive` lemma.

### EML depth hierarchy

`EMLDepth.lean` formalizes the depth-stratified EML grammar
`EML_k` and proves:

* `euler_gateway`, `euler_identity` — the Euler identity at
  depth 1 plus the constant gateway lemma.
* `exp_not_constant` — strict separation `EML_0 ⊊ EML_1`.

### Exp-log duality at fixed points

`EMLDuality.lean::exp_log_multiplier_product_at_fixed_point` —
for `z` in the slit plane with `Complex.exp z = z`, the multiplier
product `deriv exp z · deriv log z = 1`. Every Lambert-W fixed
point is therefore exp-repelling and log-attracting with
reciprocal multipliers.

### Hyperbolic functions preserve ELC

`HyperbolicPreservation.lean` — `sinh`, `cosh`, `tanh` are explicit
arithmetic combinations of `exp(±x)` and hence map ELC inputs to
ELC outputs. Includes numerical witnesses `sinh(ln 2) = 3/4`,
`cosh(ln 2) = 5/4`, and the 3-4-5 Pythagorean-triple identity
at `ln 2`.

### Infinite Zeros Barrier (Part A–C of T01)

`InfiniteZerosBarrier.lean` — `sin` is not in any finite-depth
EML grammar:

* `sin_has_infinitely_many_zeros` (0 sorry) — `sin` has
  infinitely many real zeros via `Set.infinite_of_injective_forall_mem`
  on `n ↦ nπ`.
* `analytic_finite_zeros_compact` (0 sorry) — non-zero
  real-analytic functions on `[a, b]` have finitely many zeros
  (Bolzano-Weierstrass + analytic identity theorem).
* `eml_tree_analytic`, `eml_tree_analytic_depth_le_1` (0 sorry)
  — every well-formed EML tree is real-analytic on `(0, ∞)`,
  with a complete depth-1 case analysis.

### Runtime + audit

* `Runtime.lean` — drift-aware `mg_*` operator semantics matching
  `libmonogate.h` v0.1.0; SuperBEST routing of `softplus` to
  the canonical sigmoid form, with bounds.
* `ModelAudit.lean` — SuperBEST v5.1 → v5.2 correction record:
  `sqrt = 1n` not `2n`, `mul = 1n` on the positive domain.

## Open problems

The 5 remaining sorries all sit at known Mathlib infrastructure
gaps. Sorries 1, 3, 4 reduce to the Khovanskii zero-count theorem
or o-minimality of `ℝ_exp`; Sorry 2 needs a formal `_pFq` with
DLMF parameter rewrites; Sorry 5 is a corollary of Sorry 1 and
collapses the moment Sorry 1 closes. Contributions welcome — each
one would unlock a barrier theorem of independent mathematical
interest.

### Sorry 1 — `ChainOrderAdditivity.lean::chain_order_additivity`

**Statement.** For any symbolic expression `f`, the Pfaffian
chain order of `f` equals the sum (with multiplicity) of chain
orders of its PNE-primitive AST occurrences.

**Empirical support.** 22/23 hits across two probe sets; the
single `Δ = +3` outlier is recovered once nested primitive
occurrences are counted.

**Mathlib infrastructure needed.**

* The Khovanskii zero-count theorem on Pfaffian chains.
* o-minimal structure theory for `ℝ_exp` (Wilkie 1996).
* Composition lemmas for Pfaffian functions analogous to
  `AnalyticOnNhd.comp`.

### Sorry 2 — `ChainOrderAdditivity.lean::three_tower_min_generating_set`

**Statement.** Under unrestricted parameter substitution (DLMF
identities), `{T_F, T_Γ, T_W}` is a minimum generating set for
the Pfaffian-not-elementary closure.

**Mathlib infrastructure needed.**

* A formal model of `_pFq` with parameter substitution and DLMF
  identity rewrites.
* The current statement is a placeholder pending a definition of
  "tower reducibility under parameter substitution".

### Sorry 3 — `InfiniteZerosBarrier.lean::sin_not_in_eml`

**Statement.** No finite-depth EML tree pointwise equals `Real.sin`.

**Why it matters.** Headline barrier theorem T01: every finite EML
grammar is strictly weaker than `ℝ_an,exp`.

**Mathlib infrastructure needed.**

* Khovanskii zero-count, OR
* o-minimality of `ℝ_exp` (which gives a uniform finite-zero
  bound for every definable function as a corollary).

### Sorry 4 — `InfiniteZerosBarrier.lean::sin_not_in_real_EML_k`

**Statement.** Complex-side restatement of Sorry 3:
`x ↦ sin(Re x) ∉ EML_k k` for any finite `k`.

**Mathlib infrastructure needed.** Same as Sorry 3 — both reduce
the inductive zero-count argument to a one-line consequence of an
existing meta-theorem, which Mathlib does not yet have.

### Sorry 5 — `ChainOrderAdditivity.lean::tower_base_eq_chain_order`

**Statement.** For any single-primitive expression `f` whose AST
contains exactly one PNE-primitive node `p`, the chain order of
`f` equals the chain order of `p`.

**Why it's open.** Direct corollary of Sorry 1: rewrite the chain
order via `chain_order_additivity` (which is sorry'd), then
collapse the singleton multiset sum. A theorem downstream of a
sorry is not proved — marking this as a fifth sorry keeps the
dependency on the open CHA conjecture honest.

**What closes it.** The two-line proof
`rw [chain_order_additivity, hf]; simp [Multiset.map_singleton,
Multiset.sum_singleton]` becomes a real proof the moment Sorry 1
is closed. No additional Mathlib infrastructure beyond what
Sorry 1 needs.

See [`MATHLIB_KHOVANSKII_NEEDS.md`](MATHLIB_KHOVANSKII_NEEDS.md)
for a survey of the o-minimal/Pfaffian gap and the Mathlib issues
tracking it.

## Repository layout

```
monogate-lean/
├── README.md                     -- this file
├── MATHLIB_KHOVANSKII_NEEDS.md   -- gap analysis for the 5 sorries
├── lakefile.lean
├── lean-toolchain                -- pinned at leanprover/lean4:v4.14.0
├── lake-manifest.json            -- pinned Mathlib version
├── MonogateEML.lean              -- top-level aggregator (imports all submodules)
└── MonogateEML/
    ├── AddLowerBound.lean        -- SB(add) ≥ 2
    ├── SubLowerBound.lean        -- SB(sub) ≥ 2
    ├── MulLowerBound.lean        -- SB(mul) ≥ 2
    ├── DivLowerBound.lean        -- SB(div) ≥ 2
    ├── DivLowerBound3.lean       -- extended division barrier
    ├── UpperBounds.lean          -- 1-node positive constructions
    ├── ModelAudit.lean           -- v5.1 → v5.2 correction
    ├── EMLDepth.lean             -- depth hierarchy + Euler identity
    ├── EMLDuality.lean           -- exp-log multiplier duality
    ├── HyperbolicPreservation.lean -- sinh/cosh/tanh preserve ELC
    ├── InfiniteZerosBarrier.lean -- T01, Parts A–C; Part D open
    ├── ChainOrderAdditivity.lean -- CHA + tower-base; both open
    ├── Runtime.lean              -- libmonogate semantics
    ├── Universality.lean         -- universal construction lemmas
    ├── SelfMapConjugacy.lean     -- self-map conjugacy reductions
    ├── Gamma.lean                -- Γ-function lemmas
    ├── Float64.lean              -- libm ULP postulate scaffold
    └── Tactics.lean              -- eml_auto / eml_unfold / eml_golf
```

## How to contribute

This is a research formalization, not a Mathlib-style polished
library. Contributions are welcome in any of three modes:

1. **Tighten an existing proof.** If a theorem can be shortened
   using a lemma I missed in Mathlib, send a PR — proof golfing
   is welcome. Run `lake build` clean before submitting.
2. **Close one of the four open sorries.** Each requires real
   mathematical infrastructure (Khovanskii / o-minimal / `_pFq`
   parametric DLMF). A partial proof that introduces a clean
   axiom for the missing meta-theorem is also welcome — it
   makes the dependency explicit.
3. **Upstream a small lemma to Mathlib.** Several spots in
   `EMLDuality.lean`, `HyperbolicPreservation.lean`, and
   `EMLDepth.lean` use compositions that could become Mathlib
   lemmas in their own right (e.g. `Real.exp_log_pi`). If a
   lemma here would belong upstream, send the Mathlib PR first
   and update this repo when it lands.

## License

Research formalization, all rights reserved by Monogate Research.
The proofs reference (and are licensed compatibly with) Mathlib
under Apache 2.0.

## Citation

If you use these proofs in academic work, please cite:

```bibtex
@misc{odrzywolek2026eml,
  author = {Odrzywołek, Andrzej},
  title  = {Elementary Modulo Logarithms: a Pfaffian operator algebra},
  year   = {2026},
  eprint = {2603.21852},
  archivePrefix = {arXiv}
}
```

The accompanying Lean 4 formalization lives in this repository
([github.com/agent-maestro/monogate-lean](https://github.com/agent-maestro/monogate-lean))
and is verified against the version of Mathlib pinned in
`lake-manifest.json`.
