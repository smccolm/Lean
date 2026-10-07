import Dubon2026.RectangularLatticeTransport
import Dubon2026.RectangularDualCoefficients
import Dubon2026.CuspTraceCompletedSeries

/-! # Genuine rescaled cusp coefficients identify the rectangular integral on the real axis -/

namespace Dubon2026

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

noncomputable section

/-- The rectangular dual completion includes the exact inverse-slash normalization. -/
def rectangularDualFactor (a b : ℕ) (k : ℤ) (s : ℂ) : ℂ :=
  (a : ℂ) ^ (k - 2) * cuspTraceRankinFactor (a * b) k s

/-- The actual completed rectangular lattice integral is the Dirichlet series of the actual rescaled cusp trace, with every level and Gamma factor retained. -/
theorem rectangularLatticeCuspCompleted_eq_dual_real {a b : ℕ} [NeZero a] [NeZero b] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) (hk : 0 < k) {σ : ℝ} (hσ : 1 < σ) :
    rectangularLatticeCuspCompleted f (a * b) b (Nat.pos_of_neZero _) (Nat.pos_of_neZero _) (σ : ℂ) =
      rectangularDualFactor a b k (σ : ℂ) * LSeries (rectangularDualCoefficients f) (σ : ℂ) := by
  letI : Fintype (SL(2, ℤ) ⧸ rectangularCongruenceSubgroup a b) := Subgroup.fintypeQuotientOfFiniteIndex
  rw [rectangularLatticeCuspCompleted_eq_mixedDomain f hσ,
    lattice_cusp_integral_eq_series_real (Gamma_le_rectangularCongruenceSubgroup a b)
      (center_SL_le_rectangularCongruenceSubgroup a b) (rectangularCuspForm f) hk hσ,
    rectangularDualFactor, rectangularDualCoefficients, mul_assoc]

end
end Dubon2026
