import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import RiemannZeta.CompletedZetaSymmetry
import RiemannZeta.FiniteDirichletPolynomial

open Complex BigOperators Real

noncomputable section

namespace RiemannZeta

/-- Asymmetric cross-norm product for finite Dirichlet polynomials evaluated at coordinates (σ1, t) and (σ2, -t). -/
def crossNormProduct (a : ℕ+ → ℂ) (S : Finset ℕ+) (σ1 σ2 t : ℝ) : ℝ :=
  ‖dirichletPoly a S (point σ1 t)‖ * ‖dirichletPoly (conjCoeff a) S (point σ2 (-t))‖

/-- Non-negativity of the cross-norm product: crossNormProduct(a, S, σ1, σ2, t) ≥ 0. -/
theorem crossNormProduct_nonneg (a : ℕ+ → ℂ) (S : Finset ℕ+) (σ1 σ2 t : ℝ) :
    0 ≤ crossNormProduct a S σ1 σ2 t := by
  dsimp [crossNormProduct]
  exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Double conjugation identity for coefficient sequences: (a*)*_n = a_n. -/
theorem conjCoeff_conjCoeff (a : ℕ+ → ℂ) :
    conjCoeff (conjCoeff a) = a := by
  ext n
  dsimp [conjCoeff]
  exact star_star (a n)

/-- Factor swap invariance for the cross-norm product:
    crossNormProduct(a, S, σ1, σ2, t) = crossNormProduct(a*, S, σ2, σ1, -t). -/
theorem crossNormProduct_swap (a : ℕ+ → ℂ) (S : Finset ℕ+) (σ1 σ2 t : ℝ) :
    crossNormProduct a S σ1 σ2 t = crossNormProduct (conjCoeff a) S σ2 σ1 (-t) := by
  dsimp [crossNormProduct]
  rw [neg_neg]
  rw [conjCoeff_conjCoeff]
  exact mul_comm _ _

/-- Upper bound on the absolute value of the real part of the bilinear evaluation product:
    |Re( A(σ1 + i t) · A*(σ2 - i t) )| ≤ crossNormProduct(a, S, σ1, σ2, t). -/
theorem realPart_abs_le_crossNormProduct (a : ℕ+ → ℂ) (S : Finset ℕ+) (σ1 σ2 t : ℝ) :
    |(dirichletPoly a S (point σ1 t) * dirichletPoly (conjCoeff a) S (point σ2 (-t))).re| ≤
      crossNormProduct a S σ1 σ2 t := by
  dsimp [crossNormProduct]
  have h := abs_re_le_norm (dirichletPoly a S (point σ1 t) * dirichletPoly (conjCoeff a) S (point σ2 (-t)))
  rw [norm_mul] at h
  exact h

/-- Left-factor vanishing lemma:
    If A(σ1 + i t) = 0, then crossNormProduct(a, S, σ1, σ2, t) = 0 for every σ2. -/
theorem crossNormProduct_eq_zero_of_left (a : ℕ+ → ℂ) (S : Finset ℕ+) (σ1 σ2 t : ℝ)
    (h_zero : dirichletPoly a S (point σ1 t) = 0) :
    crossNormProduct a S σ1 σ2 t = 0 := by
  dsimp [crossNormProduct]
  rw [h_zero, norm_zero, zero_mul]

/-- Right-factor vanishing lemma:
    If A*(σ2 - i t) = 0, then crossNormProduct(a, S, σ1, σ2, t) = 0 for every σ1. -/
theorem crossNormProduct_eq_zero_of_right (a : ℕ+ → ℂ) (S : Finset ℕ+) (σ1 σ2 t : ℝ)
    (h_zero : dirichletPoly (conjCoeff a) S (point σ2 (-t)) = 0) :
    crossNormProduct a S σ1 σ2 t = 0 := by
  dsimp [crossNormProduct]
  rw [h_zero, norm_zero, mul_zero]

/-- Characterization of cross-norm product vanishing:
    crossNormProduct(a, S, σ1, σ2, t) = 0 ↔ A(σ1 + i t) = 0 ∨ A*(σ2 - i t) = 0. -/
theorem crossNormProduct_eq_zero_iff (a : ℕ+ → ℂ) (S : Finset ℕ+) (σ1 σ2 t : ℝ) :
    crossNormProduct a S σ1 σ2 t = 0 ↔
      dirichletPoly a S (point σ1 t) = 0 ∨
      dirichletPoly (conjCoeff a) S (point σ2 (-t)) = 0 := by
  dsimp [crossNormProduct]
  rw [mul_eq_zero]
  rw [norm_eq_zero, norm_eq_zero]

end RiemannZeta
