import Dubon2026.PhaseDerivatives

/-! # Holomorphic phase parameters for the actual twisted Dirichlet polynomial -/

namespace Dubon2026

open Complex
open scoped BigOperators Topology

noncomputable section

/-- Extend the genuine prime phases to complex parameters. -/
def complexPhaseCoefficients (a : ℕ → ℂ) (N : ℕ)
    (x : PrimeCoordinate N → ℂ) (n : ℕ) : ℂ :=
  a n * bohrMonomial N n (fun p => Complex.exp (2 * Real.pi * Complex.I * x p))

/-- The finite Dirichlet polynomial with holomorphically extended phase coefficients. -/
def complexPhaseFamily (a : ℕ → ℂ) (N : ℕ)
    (xs : (PrimeCoordinate N → ℂ) × ℂ) : ℂ :=
  dirichletSum (complexPhaseCoefficients a N xs.1) N xs.2

theorem complexPhaseCoefficients_one (a : ℕ → ℂ) (N : ℕ)
    (x : PrimeCoordinate N → ℂ) : complexPhaseCoefficients a N x 1 = a 1 := by
  simp [complexPhaseCoefficients, bohrMonomial]

theorem complexPhaseCoefficients_real (a : ℕ → ℂ) (N : ℕ)
    (x : PrimeCoordinate N → ℝ) :
    complexPhaseCoefficients a N (fun p => (x p : ℂ)) =
      twistedCoefficients a N (fun p => (x p : UnitAddCircle)) := by
  funext n
  simp only [complexPhaseCoefficients, twistedCoefficients, fourier_coe_apply,
    Int.cast_one, mul_one, Complex.ofReal_one, div_one]

theorem complexPhaseFamily_real (a : ℕ → ℂ) (N : ℕ)
    (x : PrimeCoordinate N → ℝ) (s : ℂ) :
    complexPhaseFamily a N ((fun p => (x p : ℂ)), s) =
      dirichletSum (twistedCoefficients a N (fun p => (x p : UnitAddCircle))) N s := by
  rw [complexPhaseFamily, complexPhaseCoefficients_real]

theorem analyticAt_complexPhaseCoefficients (a : ℕ → ℂ) (N n : ℕ)
    (x : PrimeCoordinate N → ℂ) : AnalyticAt ℂ (fun y => complexPhaseCoefficients a N y n) x := by
  unfold complexPhaseCoefficients bohrMonomial
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro p _
  exact ((analyticAt_const.mul ((ContinuousLinearMap.proj p).analyticAt x)).cexp').pow _

theorem analyticAt_complexPhaseFamily (a : ℕ → ℂ) (N : ℕ)
    (xs : (PrimeCoordinate N → ℂ) × ℂ) : AnalyticAt ℂ (complexPhaseFamily a N) xs := by
  have he : complexPhaseFamily a N = (fun ys => ∑ n ∈ Finset.Icc 1 N,
      complexPhaseCoefficients a N ys.1 n * Complex.exp (-ys.2 * (Real.log n : ℂ))) := by
    funext ys
    exact dirichletSum_eq_sum_exp _ _ _
  rw [he]
  apply Finset.analyticAt_fun_sum
  intro n _
  exact ((analyticAt_complexPhaseCoefficients a N n xs.1).comp analyticAt_fst).mul
    ((analyticAt_snd.neg.mul analyticAt_const).cexp')

theorem complexPhaseFamily_not_identically_zero {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (x : PrimeCoordinate N → ℂ) :
    ∃ s : ℂ, complexPhaseFamily a N (x, s) ≠ 0 := by
  by_contra h
  push Not at h
  apply dirichletSum_ne_zero_function hN (by rwa [complexPhaseCoefficients_one]
    : complexPhaseCoefficients a N x 1 ≠ 0)
  exact funext h

end

end Dubon2026
