import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.RingTheory.PowerSeries.PiTopology
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpansion_discriminant_eq_X_mul_tprod

open scoped PowerSeries.WithPiTopology
theorem ModularCurve.qExpansion_discriminant_eq_X_mul_tprod : UpperHalfPlane.qExpansion 1 ModularForm.discriminant = PowerSeries.X * ∏' n : ℕ, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpansion_discriminant_eq_X_mul_tprod.solution
