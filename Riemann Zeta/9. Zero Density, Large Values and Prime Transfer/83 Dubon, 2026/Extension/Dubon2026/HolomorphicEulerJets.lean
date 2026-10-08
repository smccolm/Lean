import Dubon2026.AdelicUnipotentJetBounds

/-! # Genuine holomorphic Euler derivatives and their uniform original jet bounds -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Filter
open scoped Topology

/-- The original holomorphic differential expression a F(z) + z F'(z). -/
def holomorphicEulerOperator (a : ℂ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  a * F z + z * deriv F z

/-- The actual Euler differential expression remains holomorphic on the original upper half-plane. -/
theorem holomorphicEulerOperator_holomorphic (a : ℂ) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) :
    DifferentiableOn ℂ (holomorphicEulerOperator a F) upperHalfPlaneSet :=
  (hF.const_mul a).add (differentiableOn_id.mul (hF.deriv isOpen_upperHalfPlaneSet))

/-- Every genuine complex jet of the original Euler expression has its exact two-term formula. -/
theorem holomorphicEulerOperator_iteratedDeriv (a : ℂ) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (m : ℕ) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    iteratedDeriv m (holomorphicEulerOperator a F) z =
      (a + (m : ℂ)) * iteratedDeriv m F z + z * iteratedDeriv (m + 1) F z := by
  induction m generalizing z with
  | zero => simp [holomorphicEulerOperator, iteratedDeriv_zero, iteratedDeriv_succ]
  | succ m ih =>
    have he : iteratedDeriv m (holomorphicEulerOperator a F) =ᶠ[𝓝 z]
        (fun w => (a + (m : ℂ)) * iteratedDeriv m F w + w * iteratedDeriv (m + 1) F w) := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
      exact ih hw
    rw [iteratedDeriv_succ, he.deriv_eq]
    have h₀ := ((holomorphic_iteratedDeriv_upper hF m).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds hz)).hasDerivAt
    have h₁ := ((holomorphic_iteratedDeriv_upper hF (m + 1)).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds hz)).hasDerivAt
    have hd := ((h₀.const_mul (a + (m : ℂ))).add ((hasDerivAt_id z).mul h₁)).deriv
    refine hd.trans ?_
    simp only [iteratedDeriv_succ, Nat.cast_add, Nat.cast_one, id_eq]
    ring

/-- Repeated application of the genuine holomorphic Euler differential operator. -/
def holomorphicEulerIterate (a : ℂ) : ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, F => F
  | n + 1, F => holomorphicEulerOperator a (holomorphicEulerIterate a n F)

/-- Every iterated original Euler expression remains holomorphic. -/
theorem holomorphicEulerIterate_holomorphic (a : ℂ) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (n : ℕ) :
    DifferentiableOn ℂ (holomorphicEulerIterate a n F) upperHalfPlaneSet := by
  induction n with
  | zero => exact hF
  | succ n ih => exact holomorphicEulerOperator_holomorphic a ih

/-- The explicit nonnegative majorant obtained by the exact two-term Euler jet recurrence. -/
def holomorphicEulerJetBound (a : ℂ) (C : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, m => C m
  | n + 1, m => ‖a + (m : ℂ)‖ * holomorphicEulerJetBound a C n m +
      holomorphicEulerJetBound a C n (m + 1)

/-- Every Euler jet majorant is nonnegative when the original jet bounds are nonnegative. -/
theorem holomorphicEulerJetBound_nonneg (a : ℂ) (C : ℕ → ℝ) (hC : ∀ m, 0 ≤ C m)
    (n m : ℕ) : 0 ≤ holomorphicEulerJetBound a C n m := by
  induction n generalizing m with
  | zero => exact hC m
  | succ n ih => exact add_nonneg (mul_nonneg (norm_nonneg _) (ih m)) (ih (m + 1))

/-- Bounds for the original holomorphic jets control every genuine iterated Euler jet without an additional analytic assumption. -/
theorem holomorphicEulerIterate_jet_bound (a : ℂ) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (C : ℕ → ℝ)
    (hC : ∀ m, ‖iteratedDeriv m F Complex.I‖ ≤ C m) (n m : ℕ) :
    ‖iteratedDeriv m (holomorphicEulerIterate a n F) Complex.I‖ ≤
      holomorphicEulerJetBound a C n m := by
  induction n generalizing m with
  | zero => exact hC m
  | succ n ih =>
    change ‖iteratedDeriv m (holomorphicEulerOperator a (holomorphicEulerIterate a n F)) Complex.I‖ ≤ _
    rw [holomorphicEulerOperator_iteratedDeriv a (holomorphicEulerIterate_holomorphic a hF n)
      m (by simp)]
    apply (norm_add_le _ _).trans
    simp only [norm_mul, Complex.norm_I, one_mul, holomorphicEulerJetBound]
    exact add_le_add (mul_le_mul_of_nonneg_left (ih m) (norm_nonneg _)) (ih (m + 1))

end
end Dubon2026
