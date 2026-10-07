import Dubon2026.RectangularConjugation
import Dubon2026.CuspTraceRankinConvolution

/-! # Actual dual Rankin coefficients from the rescaled original cusp form -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- The actual positive mixed congruence subgroup has a finite integral coset space. -/
local instance rectangularDualCosetsFintype (a b : ℕ) [NeZero a] [NeZero b] :
    Fintype (SL(2, ℤ) ⧸ rectangularCongruenceSubgroup a b) := Subgroup.fintypeQuotientOfFiniteIndex

/-- The actual common-period finite cusp trace after diagonal rescaling, convolved with the full-level principal squares. -/
def rectangularDualCoefficients {a b : ℕ} [NeZero a] [NeZero b] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) : ℕ → ℂ :=
  cuspTraceRankinCoefficients (Gamma_le_rectangularCongruenceSubgroup a b) (rectangularCuspForm f)

/-- The actual rescaled dual coefficient is the literal convolution of all its genuine cusp expansions. -/
theorem rectangularDualCoefficients_eq {a b : ℕ} [NeZero a] [NeZero b] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) (n : ℕ) :
    rectangularDualCoefficients f n = ∑ uv ∈ n.divisorsAntidiagonal,
      principalSquareCoefficients 1 uv.1 *
        ((∑ q : SL(2, ℤ) ⧸ rectangularCongruenceSubgroup a b,
          ‖normalizedCuspPeriodCoefficients
            (cuspCosetFamily (Gamma_le_rectangularCongruenceSubgroup a b) (rectangularCuspForm f) q)
            (a * b) uv.2‖ ^ 2 : ℝ) : ℂ) := by
  simpa only [rectangularDualCoefficients, cuspTraceSquareCoefficients, Nat.cast_mul] using
    cuspTraceRankinCoefficients_eq (Gamma_le_rectangularCongruenceSubgroup a b) (rectangularCuspForm f) n

/-- Every actual rectangular dual coefficient is real and nonnegative, and its zero coefficient vanishes. -/
theorem rectangularDualCoefficients_positive {a b : ℕ} [NeZero a] [NeZero b] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) :
    rectangularDualCoefficients f 0 = 0 ∧
      (∀ n, 0 ≤ (rectangularDualCoefficients f n).re) ∧
      (∀ n, (rectangularDualCoefficients f n).im = 0) :=
  ⟨cuspTraceRankinCoefficients_zero _ _, cuspTraceRankinCoefficients_re_nonneg _ _,
    cuspTraceRankinCoefficients_im _ _⟩

/-- The original cusp form alone supplies the genuine dual-coefficient linear summatory bound. -/
theorem exists_rectangularDual_sum_upper {a b : ℕ} [NeZero a] [NeZero b] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.Icc 1 X, (rectangularDualCoefficients f n).re) ≤ C * X :=
  exists_cuspTraceRankin_sum_upper _ _ hk

/-- The genuine rescaled dual Dirichlet series converges throughout Re(s)>1. -/
theorem rectangularDual_lseriesSummable {a b : ℕ} [NeZero a] [NeZero b] {k : ℤ}
    (f : CuspForm ((Gamma0 (a * b)).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (rectangularDualCoefficients f) s := cuspTraceRankin_lseriesSummable _ _ hk hs

end
end Dubon2026
