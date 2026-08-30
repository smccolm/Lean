import RiemannZeta.GuthMaynard.TwistedMoment

open Complex Finset MeasureTheory
open scoped BigOperators Interval

namespace RiemannZeta.GuthMaynard

/-!
# Finite diagonal in the twisted fourth moment

This file isolates the exact `h * m = k * n` diagonal that appears after a
smooth approximate functional equation is expanded.  It contains no
off-diagonal estimate and makes no use of the Duke--Friedlander--Iwaniec
quadratic-divisor theorem.
-/

/-- The multiplicative oscillation in a fourfold Dirichlet expansion. -/
noncomputable def twistedFourthMomentPhase
    (h m k n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp ((((t * Real.log
    (((h * m : ℕ) : ℝ) / ((k * n : ℕ) : ℝ)) : ℝ) : ℂ) * I))

/-- On the exact Hughes--Young diagonal `hm = kn`, the full oscillatory
factor is identically one. -/
theorem twistedFourthMomentPhase_eq_one_of_diagonal
    {h m k n : ℕ} (t : ℝ) (hDiagonal : h * m = k * n) :
    twistedFourthMomentPhase h m k n t = 1 := by
  unfold twistedFourthMomentPhase
  rw [hDiagonal]
  by_cases hzero : k * n = 0
  · simp [hzero]
  · simp

/-- The diagonal phase integrates to the exact length `5T/2` of the source
interval `[T/2,3T]`. -/
theorem integral_twistedFourthMomentPhase_of_diagonal
    {h m k n : ℕ} (T : ℝ) (hDiagonal : h * m = k * n) :
    (∫ t in T / 2..3 * T, twistedFourthMomentPhase h m k n t) =
      ((5 * T / 2 : ℝ) : ℂ) := by
  calc
    (∫ t in T / 2..3 * T, twistedFourthMomentPhase h m k n t) =
        ∫ _t in T / 2..3 * T, (1 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      exact twistedFourthMomentPhase_eq_one_of_diagonal t hDiagonal
    _ = ((5 * T / 2 : ℝ) : ℂ) := by
      simp
      ring

/-- A completely finite diagonal contribution with a general complex
coefficient array.  The four finite index sets allow later AFE code to use
different smooth truncations without changing the diagonal lemma. -/
noncomputable def finiteTwistedFourthMomentDiagonal
    (T : ℝ) (H M K N : Finset ℕ)
    (a : ℕ → ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ h ∈ H, ∑ m ∈ M, ∑ k ∈ K, ∑ n ∈ N,
    if h * m = k * n then
      a h m k n *
        ∫ t in T / 2..3 * T, twistedFourthMomentPhase h m k n t
    else 0

/-- The associated finite coefficient sum on the exact diagonal. -/
noncomputable def finiteTwistedDiagonalCoefficientSum
    (H M K N : Finset ℕ) (a : ℕ → ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ h ∈ H, ∑ m ∈ M, ∑ k ∈ K, ∑ n ∈ N,
    if h * m = k * n then a h m k n else 0

/-- Exact evaluation of the complete finite diagonal after termwise
integration. -/
theorem finiteTwistedFourthMomentDiagonal_eq
    (T : ℝ) (H M K N : Finset ℕ)
    (a : ℕ → ℕ → ℕ → ℕ → ℂ) :
    finiteTwistedFourthMomentDiagonal T H M K N a =
      ((5 * T / 2 : ℝ) : ℂ) *
        finiteTwistedDiagonalCoefficientSum H M K N a := by
  unfold finiteTwistedFourthMomentDiagonal finiteTwistedDiagonalCoefficientSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hDiagonal : h * m = k * n
  · simp only [hDiagonal, if_true]
    rw [integral_twistedFourthMomentPhase_of_diagonal T hDiagonal]
    ring
  · simp [hDiagonal]

/-- Norm form of the finite diagonal bound.  All analytic work is now
concentrated in bounding the explicit coefficient sum produced by the AFE. -/
theorem norm_finiteTwistedFourthMomentDiagonal_le
    (T : ℝ) (H M K N : Finset ℕ)
    (a : ℕ → ℕ → ℕ → ℕ → ℂ) :
    ‖finiteTwistedFourthMomentDiagonal T H M K N a‖ ≤
      |5 * T / 2| *
        ∑ h ∈ H, ∑ m ∈ M, ∑ k ∈ K, ∑ n ∈ N,
          if h * m = k * n then ‖a h m k n‖ else 0 := by
  rw [finiteTwistedFourthMomentDiagonal_eq, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  unfold finiteTwistedDiagonalCoefficientSum
  calc
    ‖∑ h ∈ H, ∑ m ∈ M, ∑ k ∈ K, ∑ n ∈ N,
        if h * m = k * n then a h m k n else 0‖
        ≤ ∑ h ∈ H, ‖∑ m ∈ M, ∑ k ∈ K, ∑ n ∈ N,
            if h * m = k * n then a h m k n else 0‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ H, ∑ m ∈ M, ‖∑ k ∈ K, ∑ n ∈ N,
            if h * m = k * n then a h m k n else 0‖ := by
      gcongr with h hh
      exact norm_sum_le _ _
    _ ≤ ∑ h ∈ H, ∑ m ∈ M, ∑ k ∈ K, ‖∑ n ∈ N,
            if h * m = k * n then a h m k n else 0‖ := by
      gcongr with h hh m hm
      exact norm_sum_le _ _
    _ ≤ ∑ h ∈ H, ∑ m ∈ M, ∑ k ∈ K, ∑ n ∈ N,
          if h * m = k * n then ‖a h m k n‖ else 0 := by
      gcongr with h hh m hm k hk
      calc
        ‖∑ n ∈ N, if h * m = k * n then a h m k n else 0‖
            ≤ ∑ n ∈ N, ‖if h * m = k * n then a h m k n else 0‖ :=
              norm_sum_le _ _
        _ = ∑ n ∈ N, if h * m = k * n then ‖a h m k n‖ else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          split_ifs <;> simp

end RiemannZeta.GuthMaynard
