-- MonogateEML/SelfMapConjugacy.lean
-- Formalizes Prop A-1 (Blind omnibus session A, 2026-04-22/23):
--
-- The F16 self-maps EAL(x,x) = exp(x) + ln(x) and EXL(y,y) = exp(y) · ln(y)
-- are topologically conjugate via the real exponential.
-- Symbolically: g ∘ exp = exp ∘ f on (0, ∞), where f = EAL self-map,
-- g = EXL self-map.
--
-- The same algebra pairs EML(x,x) = exp(x) − ln(x) with
-- EDL(y,y) = exp(y) / ln(y).
--
-- These conjugacies explain the Blind Session 01 observation that EAL and
-- EXL self-maps have identical multipliers (4.3164206…) at their distinct
-- fixed points: by conjugacy, they share every dynamical invariant.
--
-- Session: blind-exploration follow-up; not yet user-verified in VS Code.
-- T_EAL_EXL_CONJ / T_EML_EDL_CONJ

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace MonogateSelfMapConjugacy

/-- **EAL↔EXL conjugacy via exp.** Let `f(x) = exp(x) + ln(x)` be the EAL
self-map (the value of the F16 operator `EAL` evaluated on the diagonal)
and `g(y) = exp(y) · ln(y)` the EXL self-map. Then on the positive reals,
`g(exp(x)) = exp(f(x))`.

This is the identity `exp(exp(x) + ln(x)) = exp(exp(x)) · x = exp(exp(x)) · ln(exp(x))`.
-/
theorem eal_exl_conjugacy (x : ℝ) (hx : 0 < x) :
    Real.exp (Real.exp x) * Real.log (Real.exp x)
      = Real.exp (Real.exp x + Real.log x) := by
  rw [Real.exp_add, Real.log_exp, Real.exp_log hx]

/-- **EML↔EDL conjugacy via exp.** Let `f(x) = exp(x) − ln(x)` be the EML
self-map and `g(y) = exp(y) / ln(y)` the EDL self-map. Then on the
positive reals with `x ≠ 1` (so `ln(x) ≠ 0`), `g(exp(x)) = exp(f(x))`.

This is the identity `exp(exp(x) − ln(x)) = exp(exp(x)) / x = exp(exp(x)) / ln(exp(x))`.
-/
theorem eml_edl_conjugacy (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) :
    Real.exp (Real.exp x) / Real.log (Real.exp x)
      = Real.exp (Real.exp x - Real.log x) := by
  have h_log_ne : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx hx1
  rw [Real.exp_sub, Real.log_exp, Real.exp_log hx]

/-- Corollary: the pairing of fixed points. If `x*` is a fixed point of the
EAL self-map (so `exp(x*) + ln(x*) = x*` on `(0, ∞)`), then `exp(x*)` is a
fixed point of the EXL self-map. -/
theorem eal_exl_fixed_point_pairing (x : ℝ) (hx : 0 < x)
    (h_fp : Real.exp x + Real.log x = x) :
    Real.exp (Real.exp x) * Real.log (Real.exp x) = Real.exp x := by
  rw [eal_exl_conjugacy x hx, h_fp]

/-- The orbit of `g = EXL self-map` starting at `exp(x)` is the `exp`-image
of the orbit of `f = EAL self-map` starting at `x`, step by step.
Stated as the single-step conjugacy: one application of `g` on `exp(x)`
is the `exp` of one application of `f` on `x`. (Iteration is handled by
repeated application.) -/
theorem eal_exl_single_step_conjugacy (x : ℝ) (hx : 0 < x) :
    (fun y => Real.exp y * Real.log y) (Real.exp x)
      = Real.exp ((fun x => Real.exp x + Real.log x) x) := by
  exact eal_exl_conjugacy x hx

end MonogateSelfMapConjugacy
