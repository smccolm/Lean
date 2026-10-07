import Dubon2026.ComplexPhaseFamily
import Mathlib.Topology.ContinuousMap.Units

/-! # The phase family in the Banach algebra of continuous functions on a compact space -/

namespace Dubon2026

open Complex
open scoped BigOperators Topology

noncomputable section

variable {K : Type*} [TopologicalSpace K]

/-- A fixed exponential along a continuous compactly parameterized path. -/
def compactDirichletTerm (γ : C(K, ℂ)) (n : ℕ) : C(K, ℂ) :=
  ⟨fun t => Complex.exp (-γ t * (Real.log n : ℂ)), by fun_prop⟩

/-- The actual phase family as a function with the uniform norm. -/
def compactPhaseFamily (a : ℕ → ℂ) (N : ℕ) (γ : C(K, ℂ))
    (x : PrimeCoordinate N → ℂ) : C(K, ℂ) :=
  ∑ n ∈ Finset.Icc 1 N, complexPhaseCoefficients a N x n • compactDirichletTerm γ n

/-- Its derivative in the Dirichlet variable, restricted to the same compact path. -/
def compactPhaseDerivative (a : ℕ → ℂ) (N : ℕ) (γ : C(K, ℂ))
    (x : PrimeCoordinate N → ℂ) : C(K, ℂ) :=
  ∑ n ∈ Finset.Icc 1 N,
    (complexPhaseCoefficients a N x n * (-(Real.log n : ℂ))) • compactDirichletTerm γ n

theorem compactPhaseFamily_apply (a : ℕ → ℂ) (N : ℕ) (γ : C(K, ℂ))
    (x : PrimeCoordinate N → ℂ) (t : K) :
    compactPhaseFamily a N γ x t = complexPhaseFamily a N (x, γ t) := by
  simp [compactPhaseFamily, complexPhaseFamily, dirichletSum_eq_sum_exp,
    compactDirichletTerm, smul_eq_mul]

theorem compactPhaseDerivative_apply (a : ℕ → ℂ) (N : ℕ) (γ : C(K, ℂ))
    (x : PrimeCoordinate N → ℂ) (t : K) :
    compactPhaseDerivative a N γ x t = deriv (dirichletSum (complexPhaseCoefficients a N x) N) (γ t) := by
  simp [compactPhaseDerivative, compactDirichletTerm, smul_eq_mul,
    (hasDerivAt_dirichletSum_exp _ _ _).deriv]

variable [CompactSpace K]

theorem analyticAt_compactPhaseFamily (a : ℕ → ℂ) (N : ℕ) (γ : C(K, ℂ))
    (x : PrimeCoordinate N → ℂ) : AnalyticAt ℂ (compactPhaseFamily a N γ) x := by
  unfold compactPhaseFamily
  apply Finset.analyticAt_fun_sum
  intro n _
  exact (analyticAt_complexPhaseCoefficients a N n x).smul analyticAt_const

theorem analyticAt_compactPhaseDerivative (a : ℕ → ℂ) (N : ℕ) (γ : C(K, ℂ))
    (x : PrimeCoordinate N → ℂ) : AnalyticAt ℂ (compactPhaseDerivative a N γ) x := by
  unfold compactPhaseDerivative
  apply Finset.analyticAt_fun_sum
  intro n _
  exact ((analyticAt_complexPhaseCoefficients a N n x).mul analyticAt_const).smul analyticAt_const

/-- Banach-algebra logarithmic derivative; it agrees with the pointwise one near a zero-free path. -/
def compactPhaseLogDeriv (a : ℕ → ℂ) (N : ℕ) (γ : C(K, ℂ))
    (x : PrimeCoordinate N → ℂ) : C(K, ℂ) :=
  compactPhaseDerivative a N γ x * Ring.inverse (compactPhaseFamily a N γ x)

omit [CompactSpace K] in
theorem isUnit_compactPhaseFamily (a : ℕ → ℂ) (N : ℕ) (γ : C(K, ℂ))
    (x : PrimeCoordinate N → ℂ)
    (hn : ∀ t, complexPhaseFamily a N (x, γ t) ≠ 0) :
    IsUnit (compactPhaseFamily a N γ x) := by
  apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
  simpa only [compactPhaseFamily_apply] using hn

theorem analyticAt_compactPhaseLogDeriv (a : ℕ → ℂ) (N : ℕ) (γ : C(K, ℂ))
    (x : PrimeCoordinate N → ℂ)
    (hn : ∀ t, complexPhaseFamily a N (x, γ t) ≠ 0) :
    AnalyticAt ℂ (compactPhaseLogDeriv a N γ) x := by
  have hi := analyticOnNhd_inverse (𝕜 := ℂ) (compactPhaseFamily a N γ x)
    (isUnit_compactPhaseFamily a N γ x hn)
  exact (analyticAt_compactPhaseDerivative a N γ x).mul
    (hi.comp (analyticAt_compactPhaseFamily a N γ x))

omit [CompactSpace K] in
theorem compactPhaseLogDeriv_apply (a : ℕ → ℂ) (N : ℕ) (γ : C(K, ℂ))
    (x : PrimeCoordinate N → ℂ)
    (hn : ∀ t, complexPhaseFamily a N (x, γ t) ≠ 0) (t : K) :
    compactPhaseLogDeriv a N γ x t =
      logDeriv (dirichletSum (complexPhaseCoefficients a N x) N) (γ t) := by
  have hi := isUnit_compactPhaseFamily a N γ x hn
  have he := ContinuousMap.congr_fun (Ring.mul_inverse_cancel _ hi) t
  simp only [ContinuousMap.mul_apply, ContinuousMap.one_apply, compactPhaseFamily_apply] at he
  have hinv : Ring.inverse (compactPhaseFamily a N γ x) t =
      (complexPhaseFamily a N (x, γ t))⁻¹ := by
    apply (mul_left_cancel₀ (hn t))
    rw [he, mul_inv_cancel₀ (hn t)]
  simp only [compactPhaseLogDeriv, ContinuousMap.mul_apply, compactPhaseDerivative_apply,
    hinv, complexPhaseFamily, logDeriv_apply, div_eq_mul_inv]

end

end Dubon2026
