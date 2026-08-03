import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import ReimannZeta.PhaseWinding

open Complex BigOperators Real

noncomputable section

namespace ReimannZeta

/-- Evaluation of a Dirichlet polynomial with coefficients a_n over a finite set S at s ∈ ℂ. -/
def dirichletPoly (a : ℕ → ℂ) (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ S, a n * (n : ℂ) ^ (-s)

/-- Conjugate coefficient sequence a*_n = star (a_n). -/
def conjCoeff (a : ℕ → ℂ) : ℕ → ℂ :=
  fun n => star (a n)

/-- Dirichlet energy density at s ∈ ℂ: |A(s)|^2. -/
def dirichletEnergy (a : ℕ → ℂ) (S : Finset ℕ) (s : ℂ) : ℝ :=
  ‖dirichletPoly a S s‖ ^ 2

/-- Conjugate identity for Dirichlet polynomials: star (A(s)) = A*(star s). -/
theorem dirichletPoly_conj (a : ℕ → ℂ) (S : Finset ℕ) (s : ℂ) :
    star (dirichletPoly a S s) = dirichletPoly (conjCoeff a) S (star s) := by
  dsimp [dirichletPoly, conjCoeff]
  rw [map_sum]
  congr 1 with n
  rw [map_mul]
  congr 1
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.cast_zero]
    by_cases hs : s = 0
    · subst hs; simp
    · have h1 : -s ≠ 0 := neg_ne_zero.mpr hs
      have h2 : -star s ≠ 0 := neg_ne_zero.mpr (star_ne_zero.mpr hs)
      rw [zero_cpow h1, map_zero]
      exact (zero_cpow h2).symm
  · have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hn_arg : ((n : ℝ) : ℂ).arg ≠ π := by
      rw [arg_ofReal_of_nonneg (le_of_lt hn_pos)]
      exact Real.pi_ne_zero.symm
    have h_conj := cpow_conj ((n : ℝ) : ℂ) (-s) hn_arg
    simp only [conj_ofReal, map_neg] at h_conj
    exact h_conj.symm

/-- Energy invariance under complex conjugation: ‖A(s)‖ = ‖A*(star s)‖. -/
theorem dirichletPoly_norm_conj (a : ℕ → ℂ) (S : Finset ℕ) (s : ℂ) :
    ‖dirichletPoly a S s‖ = ‖dirichletPoly (conjCoeff a) S (star s)‖ := by
  rw [← norm_star]
  rw [dirichletPoly_conj]

/-- Dirichlet energy duality across conjugate frequency lines:
    ‖A(σ + i t)‖ = ‖A*(σ - i t)‖. -/
theorem dirichletEnergy_conj_line (a : ℕ → ℂ) (S : Finset ℕ) (σ t : ℝ) :
    dirichletEnergy a S (offLinePoint σ t) =
      dirichletEnergy (conjCoeff a) S (offLinePoint σ (-t)) := by
  dsimp [dirichletEnergy]
  have h_conj : star (offLinePoint σ t) = offLinePoint σ (-t) := by
    apply Complex.ext <;> simp [offLinePoint]
  rw [← h_conj]
  rw [← dirichletPoly_norm_conj]

/-- Large-value condition duality: |A(σ + i t)| ≥ V ↔ |A*(σ - i t)| ≥ V. -/
theorem largeValue_dual_iff (a : ℕ → ℂ) (S : Finset ℕ) (σ t V : ℝ) :
    V ≤ ‖dirichletPoly a S (offLinePoint σ t)‖ ↔
      V ≤ ‖dirichletPoly (conjCoeff a) S (offLinePoint σ (-t))‖ := by
  have h_conj : star (offLinePoint σ t) = offLinePoint σ (-t) := by
    apply Complex.ext <;> simp [offLinePoint]
  rw [← h_conj]
  rw [← dirichletPoly_norm_conj]

/-- Zero-density mollifier energy duality theorem:
    If a Dirichlet polynomial A(s) vanishes at an off-line point σ + i t,
    then its conjugate polynomial A*(s) vanishes at the conjugate point σ - i t. -/
theorem dirichletPoly_zero_dual (a : ℕ → ℂ) (S : Finset ℕ) (σ t : ℝ)
    (h_zero : dirichletPoly a S (offLinePoint σ t) = 0) :
    dirichletPoly (conjCoeff a) S (offLinePoint σ (-t)) = 0 := by
  have h_conj : star (offLinePoint σ t) = offLinePoint σ (-t) := by
    apply Complex.ext <;> simp [offLinePoint]
  rw [← h_conj]
  rw [← dirichletPoly_conj]
  rw [h_zero]
  exact star_zero ℂ

end ReimannZeta
