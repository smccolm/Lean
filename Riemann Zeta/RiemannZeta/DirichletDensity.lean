import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import RiemannZeta.PhaseWinding

open Complex BigOperators Real

noncomputable section

namespace RiemannZeta

/-- Evaluation of a Dirichlet polynomial with coefficients a_n over a finite index set S ⊂ ℕ+ of positive naturals. -/
def dirichletPoly (a : ℕ+ → ℂ) (S : Finset ℕ+) (s : ℂ) : ℂ :=
  ∑ n ∈ S, a n * (n : ℂ) ^ (-s)

/-- Conjugate coefficient sequence a*_n = star (a_n). -/
def conjCoeff (a : ℕ+ → ℂ) : ℕ+ → ℂ :=
  fun n => star (a n)

/-- Dirichlet polynomial norm-squared quantity: |A(s)|^2. -/
def dirichletNormSquare (a : ℕ+ → ℂ) (S : Finset ℕ+) (s : ℂ) : ℝ :=
  ‖dirichletPoly a S s‖ ^ 2

/-- Conjugate coefficient theorem for finite positive-index Dirichlet polynomials:
    star (A(s)) = A*(star s). -/
theorem dirichletPoly_conj (a : ℕ+ → ℂ) (S : Finset ℕ+) (s : ℂ) :
    star (dirichletPoly a S s) = dirichletPoly (conjCoeff a) S (star s) := by
  dsimp [dirichletPoly, conjCoeff]
  rw [map_sum]
  congr 1 with n
  rw [map_mul]
  congr 1
  have hn_pos : 0 < ((n : ℕ) : ℝ) := Nat.cast_pos.mpr n.pos
  have hn_arg : (((n : ℕ) : ℂ)).arg ≠ π := by
    rw [arg_ofReal_of_nonneg (le_of_lt hn_pos)]
    exact Real.pi_ne_zero.symm
  have h_conj := cpow_conj (((n : ℕ) : ℝ) : ℂ) (-s) hn_arg
  simp only [conj_ofReal, map_neg] at h_conj
  exact h_conj.symm

/-- Norm conjugation invariance for Dirichlet polynomials: ‖A(s)‖ = ‖A*(star s)‖. -/
theorem dirichletPoly_norm_conj (a : ℕ+ → ℂ) (S : Finset ℕ+) (s : ℂ) :
    ‖dirichletPoly a S s‖ = ‖dirichletPoly (conjCoeff a) S (star s)‖ := by
  rw [← norm_star]
  rw [dirichletPoly_conj]

/-- Dirichlet norm-square equality across conjugate lines: ‖A(σ + i t)‖^2 = ‖A*(σ - i t)‖^2. -/
theorem dirichletNormSquare_conj_line (a : ℕ+ → ℂ) (S : Finset ℕ+) (σ t : ℝ) :
    dirichletNormSquare a S (point σ t) =
      dirichletNormSquare (conjCoeff a) S (point σ (-t)) := by
  dsimp [dirichletNormSquare]
  rw [← star_point]
  rw [← dirichletPoly_norm_conj]

/-- Threshold condition equivalence across conjugate parameters:
    V ≤ ‖A(σ + i t)‖ ↔ V ≤ ‖A*(σ - i t)‖. -/
theorem threshold_conj_line_iff (a : ℕ+ → ℂ) (S : Finset ℕ+) (σ t V : ℝ) :
    V ≤ ‖dirichletPoly a S (point σ t)‖ ↔
      V ≤ ‖dirichletPoly (conjCoeff a) S (point σ (-t))‖ := by
  rw [← star_point]
  rw [← dirichletPoly_norm_conj]

/-- Zero conjugation preservation for finite Dirichlet polynomials:
    If A(σ + i t) = 0, then A*(σ - i t) = 0. -/
theorem dirichletPoly_zero_conj (a : ℕ+ → ℂ) (S : Finset ℕ+) (σ t : ℝ)
    (h_zero : dirichletPoly a S (point σ t) = 0) :
    dirichletPoly (conjCoeff a) S (point σ (-t)) = 0 := by
  have h_conj : dirichletPoly (conjCoeff a) S (point σ (-t)) =
      star (dirichletPoly a S (point σ t)) := by
    rw [← star_point]
    exact (dirichletPoly_conj a S (point σ t)).symm
  rw [h_conj, h_zero, star_zero]

end RiemannZeta
