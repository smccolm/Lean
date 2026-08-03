import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import RiemannZeta.PhaseWinding
import RiemannZeta.DirichletDensity

open Complex BigOperators Real

noncomputable section

namespace RiemannZeta

/-- Asymmetric cross-energy operator for Dirichlet polynomials across arbitrary off-line heights σ1, σ2. -/
def crossEnergy (a : ℕ → ℂ) (S : Finset ℕ) (σ1 σ2 t : ℝ) : ℝ :=
  ‖dirichletPoly a S (offLinePoint σ1 t)‖ * ‖dirichletPoly (conjCoeff a) S (offLinePoint σ2 (-t))‖

/-- Non-negativity of the cross-energy operator: CrossEnergy(σ1, σ2, t, A) ≥ 0. -/
theorem crossEnergy_nonneg (a : ℕ → ℂ) (S : Finset ℕ) (σ1 σ2 t : ℝ) :
    0 ≤ crossEnergy a S σ1 σ2 t := by
  dsimp [crossEnergy]
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Double conjugation identity for coefficient sequences: (a*)*_n = a_n. -/
theorem conjCoeff_conjCoeff (a : ℕ → ℂ) :
    conjCoeff (conjCoeff a) = a := by
  ext n
  dsimp [conjCoeff]
  exact star_star (a n)

/-- Asymmetric Cross-Energy Commutative Duality Theorem:
    ‖A(σ1 + i t)‖ · ‖A*(σ2 - i t)‖ = ‖A*(σ2 - i t)‖ · ‖A(σ1 + i t)‖. -/
theorem crossEnergy_duality (a : ℕ → ℂ) (S : Finset ℕ) (σ1 σ2 t : ℝ) :
    crossEnergy a S σ1 σ2 t = crossEnergy (conjCoeff a) S σ2 σ1 (-t) := by
  dsimp [dirichletEnergy, crossEnergy]
  rw [neg_neg]
  rw [conjCoeff_conjCoeff]
  exact mul_comm _ _

/-- Cross-energy lower bound via real part of the bilinear product:
    CrossEnergy(σ1, σ2, t, A) ≥ |Re(A(σ1 + i t) · A*(σ2 - i t))|. -/
theorem crossEnergy_ge_re (a : ℕ → ℂ) (S : Finset ℕ) (σ1 σ2 t : ℝ) :
    |(dirichletPoly a S (offLinePoint σ1 t) * dirichletPoly (conjCoeff a) S (offLinePoint σ2 (-t))).re| ≤
      crossEnergy a S σ1 σ2 t := by
  dsimp [crossEnergy]
  have h := abs_re_le_norm (dirichletPoly a S (offLinePoint σ1 t) * dirichletPoly (conjCoeff a) S (offLinePoint σ2 (-t)))
  rw [norm_mul] at h
  exact h

/-- Universal Zero-Locator Theorem:
    If A(s) has an off-line zero at σ1 + i t, then the cross-energy product vanishes
    unconditionally for EVERY height σ2: CrossEnergy(σ1, σ2, t, A) = 0. -/
theorem crossEnergy_zero_of_left_zero (a : ℕ → ℂ) (S : Finset ℕ) (σ1 σ2 t : ℝ)
    (h_zero : dirichletPoly a S (offLinePoint σ1 t) = 0) :
    crossEnergy a S σ1 σ2 t = 0 := by
  dsimp [crossEnergy]
  rw [h_zero, norm_zero, zero_mul]

/-- Dual Zero-Locator Theorem:
    If A*(s) has an off-line zero at σ2 - i t, then the cross-energy product vanishes
    unconditionally for EVERY height σ1: CrossEnergy(σ1, σ2, t, A) = 0. -/
theorem crossEnergy_zero_of_right_zero (a : ℕ → ℂ) (S : Finset ℕ) (σ1 σ2 t : ℝ)
    (h_zero : dirichletPoly (conjCoeff a) S (offLinePoint σ2 (-t)) = 0) :
    crossEnergy a S σ1 σ2 t = 0 := by
  dsimp [crossEnergy]
  rw [h_zero, norm_zero, mul_zero]

end RiemannZeta
