import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.Asymptotics
import Mathlib.Tactic

open Complex Finset
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-- F-07: Explicitly construct convolution coefficients for the powered polynomial. -/
noncomputable def powCoeff (N k : ℕ) (m : ℕ) (T : ℝ) : ℂ :=
  ∑ p ∈ (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))).filter (fun p => (∏ x : Fin k, p x) = m),
    ∏ x : Fin k, detectorCoeff N (p x) T

/-- Factorization count bounds. -/
def FactorizationCountBoundHypothesis : Prop :=
  ∀ (k m : ℕ) (ε : ℝ), ε > 0 →
    ∃ C : ℝ, 0 < C ∧ ((Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 m)).filter (fun p => (∏ x : Fin k, p x) = m)).card ≤ C * (m : ℝ)^ε

/-- Bound for the powered coefficients incorporating epsilon loss. -/
def PowCoeffBoundHypothesis : Prop :=
  ∀ (N k m : ℕ) (T ε : ℝ), 0 < m → T ≥ 1 → ε > 0 →
    ∃ C : ℝ, 0 < C ∧ ‖powCoeff N k m T‖ ≤ C * (m : ℝ)^ε

/-- The powered polynomial is supported on [N^k, (2N)^k] -/
noncomputable def powPoly (N k : ℕ) (s : ℂ) (T : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc (N^k) ((2*N)^k), powCoeff N k m T * (m : ℂ) ^ (-s)

/-- F-07: The power identity hypothesis. -/
def PolynomialPowerIdentityHypothesis : Prop :=
  ∀ (N k : ℕ) (s : ℂ) (T : ℝ), (detectPoly N s T) ^ k = powPoly N k s T

/--
F-07: Decomposition into O(k) dyadic blocks.
The wide support [N^k, (2N)^k] is decomposed into O(k) dyadic blocks of the form (M, 2M].
If the powered polynomial is large, one of these dyadic blocks must retain a proportionally large value.
-/
def DyadicBlockDecompositionHypothesis : Prop :=
  ∀ (N k : ℕ) (ρ : ℂ) (T V ε : ℝ), T ≥ 1 → ε > 0 → V ≥ 0 →
    V^k ≤ ‖powPoly N k ρ T‖ →
    ∃ (M : ℝ), (N^k : ℝ) ≤ M ∧ M ≤ (2*N)^k ∧
      V^k / (T^ε * k) ≤ ‖∑ m ∈ Finset.Ioc (Nat.floor M) (Nat.floor (2*M)), powCoeff N k m T * (m : ℂ) ^ (-ρ)‖

end RiemannZeta.GuthMaynard
