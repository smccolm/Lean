import Dubon2026.AdelicHolomorphicL2Curve
import Dubon2026.AdelicHilbertGeodesicSmoothness

/-! # The actual original affine orbit as a holomorphic Hilbert slice -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm

/-- The genuine upper-half-plane affine coordinate, measured from i. -/
def realAffineHolomorphicParameter (x y : ℝ) : ℂ :=
  (x : ℂ) + (Real.exp y : ℂ) * Complex.I - Complex.I

/-- The original right affine lift retains its exact half-weight factor and original slash values. -/
theorem realWeightLift_right_affine_formula (k : ℤ) (f : ℍ → ℂ)
    (g : SL(2, ℝ)) (x y : ℝ) :
    realWeightLift k f (g * realAffineMatrix x (Real.exp_pos y)) =
      (Real.exp (y * ((k : ℝ) / 2)) : ℂ) *
        ((f ∣[k] (mapGL ℝ g)) ∘ ofComplex)
          (Complex.I + realAffineHolomorphicParameter x y) := by
  rw [realWeightLift_mul, realWeightLift, realAffineMatrix_slash_apply, ← Real.exp_mul]
  congr 1
  apply congrArg (f ∣[k] (mapGL ℝ g))
  apply UpperHalfPlane.ext
  have hi : 0 < (Complex.I + realAffineHolomorphicParameter x y).im := by
    simpa [realAffineHolomorphicParameter] using Real.exp_pos y
  rw [realAffineMatrix_smul, ofComplex_apply_of_im_pos hi]
  simp only [coe_I, realAffineHolomorphicParameter]
  ring

/-- The actual original projective affine orbit is the original complex slash slice with its precise weight. -/
theorem adelicCyclicGenerator_projective_affine_formula (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (x y : ℝ) (p : AdelicProjectiveGroup) :
    adelicCyclicProjectiveFunction N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realAffineMatrix x (Real.exp_pos y)))
        (adelicCyclicGenerator N f)) p =
      (Real.exp (y * ((k : ℝ) / 2)) : ℂ) *
        adelicProjectiveHolomorphicSlice N f (realAffineHolomorphicParameter x y) p := by
  rw [adelicCyclicGenerator_projective_orbit_representative,
    canonicalAdelicGL2CuspLift_real_orbit, realWeightLift_right_affine_formula]
  rfl

/-- The original affine orbit in the genuine arithmetic L2 space equals the actual holomorphic L2 curve. -/
theorem adelicCyclicGenerator_affine_L2_formula (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (x y : ℝ)
    (hz : ‖realAffineHolomorphicParameter x y‖ < (1 / 2 : ℝ)) :
    adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realAffineMatrix x (Real.exp_pos y)))
        (adelicCyclicGenerator N f)) =
      (Real.exp (y * ((k : ℝ) / 2)) : ℂ) •
        adelicHolomorphicL2Curve N f (realAffineHolomorphicParameter x y) := by
  apply Lp.ext
  filter_upwards [(adelicCyclicProjectiveFunction_memLp_two N f _).coeFn_toLp,
    Lp.coeFn_smul (Real.exp (y * ((k : ℝ) / 2)) : ℂ)
      (adelicHolomorphicL2Curve N f (realAffineHolomorphicParameter x y)),
    adelicHolomorphicL2Curve_ae_slice N f hz] with p hp hs hh
  change (adelicCyclicProjectiveFunction_memLp_two N f _).toLp _ p = _
  rw [hp, hs, Pi.smul_apply, hh]
  exact adelicCyclicGenerator_projective_affine_formula N f x y p

/-- The actual completed affine generator orbit is the retraction of its genuine holomorphic L2 slice. -/
theorem adelicCyclicHilbertGenerator_affine_formula {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (x y : ℝ)
    (hz : ‖realAffineHolomorphicParameter x y‖ < (1 / 2 : ℝ)) :
    adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realAffineMatrix x (Real.exp_pos y)))
      (adelicCyclicHilbertGenerator f) =
      (Real.exp (y * ((k : ℝ) / 2)) : ℂ) • adelicCyclicHilbertL2Retraction f
        (adelicHolomorphicL2Curve N f (realAffineHolomorphicParameter x y)) := by
  have h := congrArg (adelicCyclicHilbertL2Retraction f)
    (adelicCyclicHilbertGenerator_orbit_toL2 f
      (adelicRealSL2Embedding (realAffineMatrix x (Real.exp_pos y))))
  rw [adelicCyclicHilbertL2Retraction_toL2, adelicCyclicGenerator_affine_L2_formula N f x y hz,
    map_smul] at h
  exact h

end
end Dubon2026
