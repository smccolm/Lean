import Dubon2026.VerticalFamily

/-! # Explicit vertical derivatives and their continuous phase dependence -/

namespace Dubon2026

open scoped BigOperators

noncomputable section

/-- The literal finite exponential formula for the kth vertical derivative. -/
def verticalJet (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (k : ℕ) (z : PrimeTorus N) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * bohrMonomial N n (fun p => fourier 1 (z p)) *
    (-Complex.I * (Real.log n : ℂ)) ^ k *
      Complex.exp (-((σ : ℂ) + Complex.I * t) * (Real.log n : ℂ))

theorem verticalJet_zero (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (z : PrimeTorus N) (t : ℝ) :
    verticalJet a N σ 0 z t = verticalFamily a N σ z t := by
  simp only [verticalFamily, dirichletSum_eq_sum_exp, twistedCoefficients,
    verticalJet, pow_zero, mul_one]

theorem hasDerivAt_verticalJet (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (k : ℕ)
    (z : PrimeTorus N) (t : ℝ) :
    HasDerivAt (fun u => verticalJet a N σ k z u) (verticalJet a N σ (k + 1) z t) t := by
  have hlin (n : ℕ) : HasDerivAt
      (fun u : ℝ => -((σ : ℂ) + Complex.I * u) * (Real.log n : ℂ))
      (-Complex.I * (Real.log n : ℂ)) t := by
    simpa using (((hasDerivAt_const t (σ : ℂ)).add
      (Complex.ofRealCLM.hasDerivAt.const_mul Complex.I)).neg.mul_const (Real.log n : ℂ))
  have hterm (n : ℕ) : HasDerivAt
      (fun u : ℝ => a n * bohrMonomial N n (fun p => fourier 1 (z p)) *
        (-Complex.I * (Real.log n : ℂ)) ^ k *
          Complex.exp (-((σ : ℂ) + Complex.I * u) * (Real.log n : ℂ)))
      (a n * bohrMonomial N n (fun p => fourier 1 (z p)) *
        (-Complex.I * (Real.log n : ℂ)) ^ (k + 1) *
          Complex.exp (-((σ : ℂ) + Complex.I * t) * (Real.log n : ℂ))) t := by
    convert (hlin n).cexp.const_mul
      (a n * bohrMonomial N n (fun p => fourier 1 (z p)) * (-Complex.I * (Real.log n : ℂ)) ^ k) using 1
    ring
  exact HasDerivAt.fun_sum (fun n (_ : n ∈ Finset.Icc 1 N) => hterm n)

theorem iteratedDeriv_verticalFamily (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (k : ℕ)
    (z : PrimeTorus N) :
    iteratedDeriv k (verticalFamily a N σ z) = verticalJet a N σ k z := by
  induction k with
  | zero =>
    rw [iteratedDeriv_zero]
    exact funext (fun t => (verticalJet_zero a N σ z t).symm)
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext (fun t => (hasDerivAt_verticalJet a N σ k z t).deriv)

theorem continuous_verticalJet (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (k : ℕ) :
    Continuous (fun zt : PrimeTorus N × ℝ => verticalJet a N σ k zt.1 zt.2) := by
  unfold verticalJet bohrMonomial
  fun_prop

theorem exists_nonzero_verticalJet {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) (z : PrimeTorus N) (t : ℝ) :
    ∃ k : ℕ, verticalJet a N σ k z t ≠ 0 := by
  simpa only [iteratedDeriv_verticalFamily] using exists_nonzero_verticalFamily_jet hN ha σ z t

end

end Dubon2026
