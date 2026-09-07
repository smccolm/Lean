import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic

open Complex

noncomputable section

namespace RiemannZeta

/-- Non-vanishing of the classical Riemann Zeta function on Re(s) ≥ 1, provided s ≠ 1.
    Derived as a coordinate wrapper around Mathlib's `riemannZeta_ne_zero_of_one_le_re`.
    Note: At s = 1, ζ(s) possesses a simple pole. Mathlib assigns a totalized value at s = 1. -/
theorem riemannZeta_ne_zero_of_re_ge_one_of_ne_one {s : ℂ} (hs : 1 ≤ s.re) (_hne : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  exact riemannZeta_ne_zero_of_one_le_re hs

/-- Classical non-vanishing of the Riemann Zeta function along the 1-line s = 1 + i t for t ≠ 0.
    The point t = 0 corresponds to the simple pole at s = 1. -/
theorem riemannZeta_ne_zero_on_one_line (t : ℝ) (_ht : t ≠ 0) :
    riemannZeta (1 + (t : ℂ) * I) ≠ 0 := by
  have h_re : 1 ≤ (1 + (t : ℂ) * I).re := by simp
  exact riemannZeta_ne_zero_of_one_le_re h_re

/-- Mathlib's totalized nonvanishing statement for all Re(s) ≥ 1 (including the assigned junk value at s = 1). -/
theorem riemannZeta_ne_zero_totalized (t : ℝ) :
    riemannZeta (1 + (t : ℂ) * I) ≠ 0 := by
  have h : 1 ≤ (1 + (t : ℂ) * I).re := by simp
  exact riemannZeta_ne_zero_of_one_le_re h

end RiemannZeta
