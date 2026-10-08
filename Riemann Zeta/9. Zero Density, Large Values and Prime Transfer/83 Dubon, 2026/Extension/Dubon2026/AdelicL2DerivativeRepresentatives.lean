import Dubon2026.AdelicProjectiveRealDerivative

/-! # The original pointwise representatives of the actual adelic L2 derivatives -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

/-- The derivative of the original quotient L2 orbit is represented almost everywhere by the actual pointwise derivative. -/
theorem adelicProjectiveRealOrbit_deriv_ae_of_bounds (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ))
    (hd : ∀ g : RationalAdelicGL2, DifferentiableAt ℝ
      (fun t : ℝ => canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (c t))) 0)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hD : ∀ g : RationalAdelicGL2, ‖deriv
      (fun t : ℝ => canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (c t))) 0‖ ≤ C)
    (hL : ∀ g : RationalAdelicGL2, ∀ t : ℝ,
      ‖canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (c t)) -
        canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (c 0))‖ ≤ C * |t|) :
    (⇑(deriv (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation (adelicRealSL2Embedding (c t))
        (adelicCyclicGenerator N f))) 0) : AdelicProjectiveGroup → ℂ) =ᵐ[
          adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)]
      (fun p => deriv (fun t : ℝ => adelicProjectiveRealOrbit N f c t p) 0) := by
  let μ := adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)
  letI : IsFiniteMeasure μ := by
    constructor
    simpa only [μ, Measure.restrict_apply_univ] using adelicProjectiveGamma0Domain_volume_lt_top N
  let F := adelicProjectiveRealOrbit N f c
  let D := fun p => deriv (fun t : ℝ => F t p) 0
  have hF (t : ℝ) : MemLp (F t) 2 μ := adelicProjectiveRealOrbit_memLp N f c t
  have hpoint (p : AdelicProjectiveGroup) : HasDerivAt (fun t : ℝ => F t p) (D p) 0 := by
    obtain ⟨g, hg⟩ := adelicProjectiveRealOrbit_representative N f c p
    have he : (fun t : ℝ => F t p) = fun t =>
        canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (c t)) := funext hg
    apply DifferentiableAt.hasDerivAt
    rw [he]
    exact hd g
  have hbound (p : AdelicProjectiveGroup) : ‖D p‖ ≤ C := by
    obtain ⟨g, hg⟩ := adelicProjectiveRealOrbit_representative N f c p
    change ‖deriv (fun t : ℝ => F t p) 0‖ ≤ C
    have he : (fun t : ℝ => F t p) = fun t =>
        canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding (c t)) := funext hg
    rw [he]
    exact hD g
  have hmem : MemLp D 2 μ := memLp_pointwise_derivative F D
    (fun t => (hF t).aestronglyMeasurable) hpoint C hbound
  have herr (t : ℝ) (p : AdelicProjectiveGroup) :
      ‖(t⁻¹ : ℝ) • (F t p - F 0 p) - D p‖ ≤ 2 * C := by
    apply difference_quotient_error_bound (fun u => F u p) (D p) hC0 _ (hbound p)
    intro u
    obtain ⟨g, hg⟩ := adelicProjectiveRealOrbit_representative N f c p
    change ‖adelicProjectiveRealOrbit N f c u p - adelicProjectiveRealOrbit N f c 0 p‖ ≤ _
    rw [hg u, hg 0]
    exact hL g u
  have hder := (hasDerivAt_toLp_of_bounded_difference_quotients F D hF hmem hpoint
    (by positivity : 0 ≤ 2 * C) herr).deriv
  change (⇑(deriv (fun t : ℝ => (hF t).toLp (F t)) 0) : AdelicProjectiveGroup → ℂ) =ᵐ[μ] D
  rw [hder]
  exact hmem.coeFn_toLp


end
end Dubon2026
