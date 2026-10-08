import Dubon2026.HolomorphicEulerJets

/-! # Every derivative of the original weighted geodesic curve -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane

/-- The actual weighted exponential curve has each genuine derivative given by the corresponding original Euler expression. -/
theorem holomorphicWeightedExponential_iteratedDeriv (a : ℝ) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (n : ℕ) :
    iteratedDeriv n (holomorphicWeightedExponential a F) =
      holomorphicWeightedExponential a (holomorphicEulerIterate (a : ℂ) n F) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, holomorphicEulerIterate]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (holomorphicWeightedExponential_hasDerivAt a
      (holomorphicEulerIterate_holomorphic (a : ℂ) hF n) t).deriv

/-- The successive original weighted exponential jets have their actual derivatives at every real parameter. -/
theorem holomorphicWeightedExponential_jet_hasDerivAt (a : ℝ) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (n : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv n (holomorphicWeightedExponential a F))
      (iteratedDeriv (n + 1) (holomorphicWeightedExponential a F) t) t := by
  rw [holomorphicWeightedExponential_iteratedDeriv a hF n,
    holomorphicWeightedExponential_iteratedDeriv a hF (n + 1)]
  exact holomorphicWeightedExponential_hasDerivAt a
    (holomorphicEulerIterate_holomorphic (a : ℂ) hF n) t

/-- At zero, every original geodesic jet is exactly its holomorphic Euler iterate at i. -/
theorem holomorphicWeightedExponential_iteratedDeriv_zero (a : ℝ) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (n : ℕ) :
    iteratedDeriv n (holomorphicWeightedExponential a F) 0 =
      holomorphicEulerIterate (a : ℂ) n F Complex.I := by
  rw [holomorphicWeightedExponential_iteratedDeriv a hF]
  simp [holomorphicWeightedExponential]

end
end Dubon2026
