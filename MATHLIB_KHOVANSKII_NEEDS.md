# Mathlib Khovanskii / o-minimal needs (2026-04-29)

This document inventories the remaining `sorry`s in the MonogateEML
Lean repository and identifies the single Mathlib gap that, once
filled, would close all four of them simultaneously.

## Current sorry inventory

After closing `Runtime.mg_softplus_route_bound_high` (a pure-ℝ
approximation bound) on 2026-04-29, the surviving sorries are:

| File | Theorem | Line | Blocker |
|---|---|---|---|
| `MonogateEML/InfiniteZerosBarrier.lean` | `sin_not_in_eml` | 326 | Khovanskii zero-count |
| `MonogateEML/InfiniteZerosBarrier.lean` | `sin_not_in_real_EML_k` | 337 | Khovanskii zero-count |
| `MonogateEML/ChainOrderAdditivity.lean` | `chain_order_additivity` | 138 | Khovanskii chain order |
| `MonogateEML/ChainOrderAdditivity.lean` | `three_tower_min_generating_set` | 175 | Parameter-substitution + placeholder predicate |

Three of the four are blocked on the same Mathlib gap. The fourth
(`three_tower_min_generating_set`) has a placeholder conclusion
(`∃ params : ℕ, True`) and needs a real predicate before it can be
proved meaningfully — see "Open: placeholder rewrite" below.

## The Mathlib gap (verified 2026-04-28)

A search of the Mathlib pinned in `lake-manifest.json` returned:

- `pfaffian` / `Pfaffian` — three hits, all algebraic false positives
  (CompleteBooleanAlgebra, OrderOfElement, PeriodicPts).
- `khovanskii` — zero hits.
- `wilkie` — one hit in `Analysis/Analytic/Polynomial.lean`, false
  positive (no theorem text matched).
- `o-minimal` / `o_minimal` / `oMinimal` — zero hits.
- No `*minimal*` directory exists.

What does exist (`Mathlib/Analysis/Analytic/IsolatedZeros.lean`) is
the principle of isolated zeros plus
`eqOn_zero_or_eventually_ne_zero_of_preconnected`. These say the
zero set of an analytic function is either everything or codiscrete
— they do **not** bound the count of zeros, which is what the four
open theorems need.

## Minimal viable contribution

The smallest Mathlib addition that closes
`sin_not_in_eml` / `sin_not_in_real_EML_k` is a quantitative
zero-count bound for Pfaffian functions of bounded chain order on
closed intervals. A possible decomposition:

- `Mathlib/Analysis/Pfaffian/Basic.lean`
  - Definition: a Pfaffian chain is a sequence
    `(f_1, ..., f_r)` of real-analytic functions on a domain `U`
    such that each `f_i'` is a polynomial in
    `(x, f_1, ..., f_i)` with coefficients in `ℝ[x]`.
  - Definition: a Pfaffian function is `q(x, f_1, ..., f_r)` for
    some polynomial `q ∈ ℝ[x, y_1, ..., y_r]` and chain
    `(f_1, ..., f_r)`.

- `Mathlib/Analysis/Pfaffian/ZeroBound.lean`
  - Khovanskii's theorem (Rolle-iteration form): the number of
    isolated real zeros of a Pfaffian function on a closed
    bounded interval is bounded by an explicit function of the
    chain order `r`, the chain degrees `α_i`, and the polynomial
    degree `β`. Reference: Khovanskii 1991, *Fewnomials*; also
    Gabrielov–Vorobjov 2004, *Complexity of computations with
    Pfaffian and Noetherian functions*.

The chain-order-1 case alone (`r = 1`) is sufficient to close
`sin_not_in_eml` for the depth-1 fragment, and would already be a
publishable Mathlib contribution.

## Closing the four sorries from the gap

| Theorem | What the gap unlocks |
|---|---|
| `sin_not_in_eml` | Each candidate EML tree of bounded depth is a Pfaffian function; bound on its zero count contradicts `sin_int_pi_zero` for the integer multiples `nπ` in any interval. |
| `sin_not_in_real_EML_k` | Same argument lifted to the complex-coerced statement; otherwise structurally identical. |
| `chain_order_additivity` | The chain order is preserved under sum / product of Pfaffian chains; combined with the AST-occurrence multiset definition this gives the additivity equation. Empirical: 22/23 hits. |
| `three_tower_min_generating_set` | Needs **both** the Pfaffian-chain machinery AND a predicate for "reducible to T_F under DLMF parameter substitution" — see below. |

## Open: placeholder rewrite

`three_tower_min_generating_set` currently has the conclusion
`∃ params : ℕ, True`, marked in source as a placeholder. The
sorry is structural — the trivial proof `⟨0, trivial⟩` would
discharge it without expressing the intended claim. A meaningful
rewrite would introduce:

- A `ParamSubstitution PNEPrimitive` predicate capturing DLMF
  parameter-substitution identities (e.g. `T_J 0 = T_F (1/2, ...)`).
- A `Reducible p q ↔ ∃ subst, q = subst p` relation.
- The intended theorem: every member of `{T_erf, T_Si, T_J, T_Ai, T_K}`
  is `Reducible` to `T_F`.

This is a meaningful but separate engineering task, independent
of Khovanskii. It can proceed in parallel.

## How to contribute

1. Search recent Mathlib PRs / Lean Zulip for active Pfaffian /
   o-minimal threads to avoid duplicate effort.
2. Open a Mathlib RFC / draft PR proposing the minimal Pfaffian
   namespace described above.
3. Reference this document in the RFC; the four open theorems in
   `MonogateEML/` are concrete consumers ready to land once the
   bound is available.

Citations:

- Khovanskii, *Fewnomials*, AMS Translations of Mathematical
  Monographs vol. 88, 1991.
- Wilkie, *Model completeness results for expansions of the
  ordered field of real numbers by restricted Pfaffian functions
  and the exponential function*, J. Amer. Math. Soc. 9 (1996).
- Gabrielov & Vorobjov, *Complexity of computations with Pfaffian
  and Noetherian functions*, in *Normal forms, bifurcations and
  finiteness problems in differential equations*, NATO Sci. Ser.
  II Math. Phys. Chem. 137, 2004.
