import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic

open Complex

noncomputable section

namespace ReimannZeta

/-- Non-vanishing of the Riemann Zeta function on Re(s) ≥ 1. -/
theorem riemannZeta_ne_zero_of_re_ge_one {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 := by
  exact riemannZeta_ne_zero_of_one_le_re hs

/-- Non-vanishing of the Riemann Zeta function along the line s = 1 + i t for t ∈ ℝ. -/
theorem riemannZeta_ne_zero_boundary (t : ℝ) :
    riemannZeta (1 + (t : ℂ) * I) ≠ 0 := by
  have h : 1 ≤ (1 + (t : ℂ) * I).re := by simp
  exact riemannZeta_ne_zero_of_re_ge_one h

end ReimannZeta
