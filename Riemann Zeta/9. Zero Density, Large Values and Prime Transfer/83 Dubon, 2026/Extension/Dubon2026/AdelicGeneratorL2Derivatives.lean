import Dubon2026.AdelicProjectiveRealDerivative

/-! # Genuine L2 differentiability of the original adelic unipotent and geodesic generator orbits -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The original adelic generator's genuine unipotent orbit is differentiable in its actual arithmetic quotient L2 norm. -/
theorem adelicCyclicGenerator_unipotent_L2_differentiableAt (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    DifferentiableAt ℝ (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicGenerator N f))) 0 := by
  obtain ⟨L, hL0, hL⟩ := canonicalAdelicGL2CuspLift_real_orbits_lipschitz N f
  obtain ⟨D, hD0, hD⟩ := canonicalAdelicGL2CuspLift_first_derivatives_bounded N f
  apply adelicProjectiveRealOrbit_differentiableAt_of_bounds N f realUpperUnipotent
    (fun g => (canonicalAdelicGL2CuspLift_unipotent_hasDerivAt N f g).differentiableAt)
    (add_nonneg hL0 hD0)
  · intro g
    rw [(canonicalAdelicGL2CuspLift_unipotent_hasDerivAt N f g).deriv]
    exact (hD g).1.trans (le_add_of_nonneg_left hL0)
  · intro g t
    have hb := (hL g t 0).1
    simp only [sub_zero] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD0) (abs_nonneg t))

/-- The original adelic generator's genuine geodesic orbit is differentiable in its actual arithmetic quotient L2 norm. -/
theorem adelicCyclicGenerator_geodesic_L2_differentiableAt (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    DifferentiableAt ℝ (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicGenerator N f))) 0 := by
  obtain ⟨L, hL0, hL⟩ := canonicalAdelicGL2CuspLift_real_orbits_lipschitz N f
  obtain ⟨D, hD0, hD⟩ := canonicalAdelicGL2CuspLift_first_derivatives_bounded N f
  apply adelicProjectiveRealOrbit_differentiableAt_of_bounds N f realGeodesicCurve
    (fun g => (canonicalAdelicGL2CuspLift_geodesic_hasDerivAt N f g).differentiableAt)
    (add_nonneg hL0 hD0)
  · intro g
    rw [(canonicalAdelicGL2CuspLift_geodesic_hasDerivAt N f g).deriv]
    exact (hD g).2.trans (le_add_of_nonneg_left hL0)
  · intro g t
    have hb := (hL g t 0).2
    simp only [sub_zero] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD0) (abs_nonneg t))

end
end Dubon2026
