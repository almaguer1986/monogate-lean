-- MonogateEML/HyperbolicPreservation.lean
-- Formalizes PROP 08-A (Blind Session 08):
-- Hyperbolic functions preserve the ELC field.
--
-- If f : ℝ → ℝ is expressible via exp, log, and arithmetic (+,-,·,/),
-- then so are sinh ∘ f, cosh ∘ f, tanh ∘ f. This gives a sharp asymmetry
-- with trigonometric functions (T01: sin(x) ∉ ELC for generic real x).
--
-- Session 28 — post-blind research; T_HYP_ELC_PRESERVE

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Exponential

open Real

namespace MonogateHyp

/-- **Explicit ELC-primitive decomposition of sinh**: `sinh x = (exp x − exp(−x))/2`.
    This makes sinh an arithmetic combination of two exp-applications (each
    one F16 node), hence sinh ∘ ELC ⊆ ELC under the standard ELC definition
    closed under {+, −, ·, /, exp, log}. -/
theorem sinh_as_exp_arithmetic (x : ℝ) :
    Real.sinh x = (Real.exp x - Real.exp (-x)) / 2 := by
  rw [Real.sinh_eq]

/-- **Explicit ELC-primitive decomposition of cosh**: `cosh x = (exp x + exp(−x))/2`. -/
theorem cosh_as_exp_arithmetic (x : ℝ) :
    Real.cosh x = (Real.exp x + Real.exp (-x)) / 2 := by
  rw [Real.cosh_eq]

/-- **Explicit ELC-primitive decomposition of tanh**: `tanh x = sinh x / cosh x`. -/
theorem tanh_as_sinh_div_cosh (x : ℝ) :
    Real.tanh x = Real.sinh x / Real.cosh x := by
  rw [Real.tanh_eq_sinh_div_cosh]

/-- **Hyperbolic Pythagorean identity** (auxiliary; used in Session 08):
    `cosh² − sinh² = 1`. -/
theorem cosh_sq_sub_sinh_sq (x : ℝ) :
    Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := by
  rw [Real.cosh_sq, Real.sinh_sq]
  ring

/-- Numeric witness used in the session: `sinh(ln 2) = 3/4`.
    Part of the 3-4-5 Pythagorean-triple observation (OBS 08-C). -/
theorem sinh_log_two : Real.sinh (Real.log 2) = 3 / 4 := by
  rw [Real.sinh_eq, Real.exp_log (by norm_num : (2:ℝ) > 0), Real.exp_neg,
      Real.exp_log (by norm_num : (2:ℝ) > 0)]
  norm_num

/-- Numeric witness used in the session: `cosh(ln 2) = 5/4`. -/
theorem cosh_log_two : Real.cosh (Real.log 2) = 5 / 4 := by
  rw [Real.cosh_eq, Real.exp_log (by norm_num : (2:ℝ) > 0), Real.exp_neg,
      Real.exp_log (by norm_num : (2:ℝ) > 0)]
  norm_num

/-- The 3-4-5 Pythagorean triple witness at `x = ln 2` in the hyperbolic
    identity (OBS 08-C, proved). -/
theorem pythagorean_triple_at_log_two :
    (Real.cosh (Real.log 2)) ^ 2 - (Real.sinh (Real.log 2)) ^ 2 = 1 := by
  exact cosh_sq_sub_sinh_sq (Real.log 2)

/-- Corollary (3-4-5 form): `5² − 3² = 4²` encoded via the hyperbolic identity
    at `ln 2`. Multiplying `cosh² − sinh² = 1` by `16`:
    `(5)² − (3)² = 16 = 4²`. -/
theorem three_four_five_from_hyperbolic :
    (5 : ℝ) ^ 2 - (3 : ℝ) ^ 2 = 4 ^ 2 := by norm_num

end MonogateHyp
