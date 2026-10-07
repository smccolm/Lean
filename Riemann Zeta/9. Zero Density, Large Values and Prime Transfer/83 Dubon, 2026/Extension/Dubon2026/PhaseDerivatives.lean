import Dubon2026.TwistCountBound

/-! # Joint continuity of the phase family and its logarithmic derivative -/

namespace Dubon2026

open Filter Set Complex
open scoped Topology BigOperators

theorem hasDerivAt_dirichletSum_exp (a : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    HasDerivAt (dirichletSum a N)
      (∑ n ∈ Finset.Icc 1 N,
        a n * (-(Real.log n : ℂ)) * Complex.exp (-s * (Real.log n : ℂ))) s := by
  have ht (n : ℕ) : HasDerivAt
      (fun w : ℂ => a n * Complex.exp (-w * (Real.log n : ℂ)))
      (a n * (-(Real.log n : ℂ)) * Complex.exp (-s * (Real.log n : ℂ))) s := by
    have hd : HasDerivAt (fun w : ℂ => -w * (Real.log n : ℂ)) (-(Real.log n : ℂ)) s := by
      simpa using (hasDerivAt_id s).neg.mul_const (Real.log n : ℂ)
    convert (hd.cexp.const_mul (a n)) using 1
    ring
  rw [show dirichletSum a N = (fun w => ∑ n ∈ Finset.Icc 1 N,
    a n * Complex.exp (-w * (Real.log n : ℂ))) from funext (dirichletSum_eq_sum_exp a N)]
  exact HasDerivAt.fun_sum (fun n (_ : n ∈ Finset.Icc 1 N) => ht n)

theorem continuous_twisted_dirichletSum_deriv (a : ℕ → ℂ) (N : ℕ) :
    Continuous (fun zs : PrimeTorus N × ℂ =>
      deriv (dirichletSum (twistedCoefficients a N zs.1) N) zs.2) := by
  simp only [(hasDerivAt_dirichletSum_exp _ _ _).deriv, twistedCoefficients, bohrMonomial]
  fun_prop

theorem continuousAt_twisted_logDeriv (a : ℕ → ℂ) (N : ℕ)
    (z : PrimeTorus N) (s : ℂ)
    (hn : dirichletSum (twistedCoefficients a N z) N s ≠ 0) :
    ContinuousAt (fun zs : PrimeTorus N × ℂ =>
      logDeriv (dirichletSum (twistedCoefficients a N zs.1) N) zs.2) (z, s) :=
  (continuous_twisted_dirichletSum_deriv a N).continuousAt.div
    (continuous_twisted_dirichletSum a N).continuousAt hn

theorem eventually_ne_zero_twist_compact (a : ℕ → ℂ) (N : ℕ)
    (z : PrimeTorus N) {K : Set ℂ} (hK : IsCompact K)
    (hn : ∀ s ∈ K, dirichletSum (twistedCoefficients a N z) N s ≠ 0) :
    ∀ᶠ w in 𝓝 z, ∀ s ∈ K, dirichletSum (twistedCoefficients a N w) N s ≠ 0 := by
  apply hK.eventually_forall_of_forall_eventually
  intro s hs
  exact (continuous_twisted_dirichletSum a N).continuousAt.eventually_ne (hn s hs)

end Dubon2026
