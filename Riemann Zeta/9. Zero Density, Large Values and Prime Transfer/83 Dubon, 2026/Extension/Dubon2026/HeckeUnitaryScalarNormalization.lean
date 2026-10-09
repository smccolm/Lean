import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Exact square-root factor in the original adelic Hecke normalization -/

namespace Dubon2026

/-- Dividing the genuine classical-to-adelic determinant factor by sqrt(p) gives exactly the unitary coefficient normalization. -/
theorem hecke_unitary_scalar_normalization (k : ℤ) {p : ℝ} (hp : 0 < p) :
    ((p ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * (Real.sqrt p : ℂ) ^ (2 - k) =
      ((p ^ (-((k : ℝ) - 1) / 2) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_zpow, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_intCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hp.le,
    ← Real.rpow_add hp]
  congr 1
  push_cast
  ring

end Dubon2026
