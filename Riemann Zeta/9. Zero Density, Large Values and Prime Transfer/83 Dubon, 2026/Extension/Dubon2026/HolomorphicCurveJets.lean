import Dubon2026.RealLiftInfinitesimal

/-! # Genuine first and second derivatives of holomorphic horizontal and weighted exponential curves -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane

/-- The original holomorphic function along the horizontal line of height one has its exact complex derivative. -/
theorem holomorphic_horizontal_hasDerivAt {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (t : ℝ) :
    HasDerivAt (fun x : ℝ => F ((x : ℂ) + Complex.I))
      (deriv F ((t : ℂ) + Complex.I)) t := by
  have hz : (t : ℂ) + Complex.I ∈ upperHalfPlaneSet := by simp
  have hd := (hF.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hz)).hasDerivAt
  have ht : HasDerivAt (fun x : ℝ => (x : ℂ) + Complex.I) 1 t := by
    simpa using Complex.ofRealCLM.hasDerivAt.add_const Complex.I
  simpa only [Function.comp_def, mul_one] using hd.comp t ht

/-- The literal horizontal curve has second derivative equal to the actual second complex derivative. -/
theorem holomorphic_horizontal_second {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) :
    deriv (deriv (fun t : ℝ => F ((t : ℂ) + Complex.I))) 0 = deriv (deriv F) Complex.I := by
  have he : deriv (fun t : ℝ => F ((t : ℂ) + Complex.I)) =
      fun t : ℝ => deriv F ((t : ℂ) + Complex.I) :=
    funext (fun t => (holomorphic_horizontal_hasDerivAt hF t).deriv)
  rw [he]
  simpa using (holomorphic_horizontal_hasDerivAt (hF.deriv isOpen_upperHalfPlaneSet) 0).deriv

/-- The actual holomorphic exponential curve with its genuine real exponential weight. -/
def holomorphicWeightedExponential (a : ℝ) (F : ℂ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (a * t) : ℂ) * F ((Real.exp t : ℂ) * Complex.I)

/-- The exact first derivative of the actual weighted exponential curve. -/
theorem holomorphicWeightedExponential_hasDerivAt (a : ℝ) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (t : ℝ) :
    HasDerivAt (holomorphicWeightedExponential a F)
      ((Real.exp (a * t) : ℂ) * ((a : ℂ) * F ((Real.exp t : ℂ) * Complex.I) +
        ((Real.exp t : ℂ) * Complex.I) * deriv F ((Real.exp t : ℂ) * Complex.I))) t := by
  have hz : (Real.exp t : ℂ) * Complex.I ∈ upperHalfPlaneSet := by
    simpa using Real.exp_pos t
  have hd := (hF.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hz)).hasDerivAt
  have ht : HasDerivAt (fun x : ℝ => (Real.exp x : ℂ) * Complex.I)
      ((Real.exp t : ℂ) * Complex.I) t :=
    (Real.hasDerivAt_exp t).ofReal_comp.mul_const Complex.I
  have he := hd.comp t ht
  have hw : HasDerivAt (fun x : ℝ => (Real.exp (a * x) : ℂ))
      ((a : ℂ) * (Real.exp (a * t) : ℂ)) t := by
    simpa [mul_comm] using (((hasDerivAt_id t).const_mul a).exp).ofReal_comp
  convert hw.mul he using 1
  dsimp only [Function.comp_def]
  ring

/-- The exact second derivative includes the original function and its first two complex derivatives. -/
theorem holomorphicWeightedExponential_second (a : ℝ) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) :
    deriv (deriv (holomorphicWeightedExponential a F)) 0 =
      (a : ℂ) ^ 2 * F Complex.I + (2 * (a : ℂ) + 1) * Complex.I * deriv F Complex.I -
        deriv (deriv F) Complex.I := by
  have heq : deriv (holomorphicWeightedExponential a F) = fun t : ℝ =>
      (Real.exp (a * t) : ℂ) * ((a : ℂ) * F ((Real.exp t : ℂ) * Complex.I) +
        ((Real.exp t : ℂ) * Complex.I) * deriv F ((Real.exp t : ℂ) * Complex.I)) :=
    funext (fun t => (holomorphicWeightedExponential_hasDerivAt a hF t).deriv)
  rw [heq]
  have hi : Complex.I ∈ upperHalfPlaneSet := by simp
  have hd := (hF.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hi)).hasDerivAt
  have hd' := ((hF.deriv isOpen_upperHalfPlaneSet).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds hi)).hasDerivAt
  have ht : HasDerivAt (fun t : ℝ => (Real.exp t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (Real.hasDerivAt_exp 0).ofReal_comp.mul_const Complex.I
  have he := hd.comp_of_eq 0 ht (by simp)
  have he' := hd'.comp_of_eq 0 ht (by simp)
  have hw : HasDerivAt (fun t : ℝ => (Real.exp (a * t) : ℂ)) (a : ℂ) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul a).exp).ofReal_comp
  have hp := (hw.mul ((he.const_mul (a : ℂ)).add (ht.mul he'))).deriv
  simp only [Function.comp_def, Pi.mul_apply, Pi.add_apply, mul_zero,
    Real.exp_zero, Complex.ofReal_one, one_mul] at hp
  refine hp.trans ?_
  linear_combination (deriv (deriv F) Complex.I) * Complex.I_sq

end
end Dubon2026
