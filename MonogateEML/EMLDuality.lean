-- MonogateEML/EMLDuality.lean
-- Formalizes PROP 02-B (Blind Session 02):
-- The exp–log multiplier product at any fixed point of exp equals 1.
-- I.e. if Complex.exp z = z then exp'(z) · log'(z) = 1.
--
-- This is the structural duality observed empirically for the Lambert
-- fixed points z_k* = -W_k(-1) in Blind Session 02/03.
--
-- Session 28 — post-blind research; T_EXP_LOG_DUALITY

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Complex

/-- Any fixed point of `Complex.exp` is non-zero (since `Complex.exp` has no zeros). -/
lemma exp_fixed_point_ne_zero {z : ℂ} (hz : Complex.exp z = z) : z ≠ 0 := by
  intro hz0
  have : Complex.exp z = 0 := by rw [hz]; exact hz0
  exact Complex.exp_ne_zero z this

/-- Pointwise form of `Complex.deriv_exp`. -/
lemma deriv_exp_at (z : ℂ) : deriv Complex.exp z = Complex.exp z :=
  (Complex.hasDerivAt_exp z).deriv

/-- Pointwise form of the complex-log derivative (slit-plane). -/
lemma deriv_log_at {z : ℂ} (hdom : z ∈ Complex.slitPlane) :
    deriv Complex.log z = z⁻¹ :=
  (Complex.hasDerivAt_log hdom).deriv

/-- Corollary: the fixed-point multiplier of `Complex.exp` at `z*` is exactly
    `z*` itself, so `|mult_exp| = |z*|`. -/
theorem exp_fixed_point_multiplier_equals_z
    {z : ℂ} (hz : Complex.exp z = z) :
    deriv Complex.exp z = z := by
  rw [deriv_exp_at, hz]

/-- The log-multiplier at any slit-plane point is the reciprocal. -/
theorem log_multiplier_at_exp_fixed_point
    {z : ℂ} (_hz : Complex.exp z = z) (hdom : z ∈ Complex.slitPlane) :
    deriv Complex.log z = z⁻¹ :=
  deriv_log_at hdom

/-- **PROP 02-B**: The multiplier product `(exp)'(z) · (log)'(z)` equals 1
    at any fixed point of `exp` lying in the slit plane (where `log` is
    differentiable).

    Empirically verified in Blind Session 02 for the Lambert fixed points
    `z_k* = -W_k(-1)`: they are all repelling under exp (|mult| = |z_k*| > 1)
    and attracting under log (|mult| = 1/|z_k*| < 1), with product exactly 1. -/
theorem exp_log_multiplier_product_at_fixed_point
    {z : ℂ} (hz : Complex.exp z = z) (hdom : z ∈ Complex.slitPlane) :
    deriv Complex.exp z * deriv Complex.log z = 1 := by
  have hne : z ≠ 0 := exp_fixed_point_ne_zero hz
  rw [deriv_exp_at, deriv_log_at hdom, hz]
  field_simp
