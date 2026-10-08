import Dubon2026.AdelicAffineHolomorphicFormula

/-! # The actual original real-group orbit as a genuine holomorphic Hilbert slice -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm

/-- The genuine real-group orbit of i, measured from i in the complex plane. -/
def realGroupHolomorphicParameter (h : SL(2, ℝ)) : ℂ := (h • I : ℍ) - Complex.I

/-- The literal original real-group lift is its original slash slice times the exact automorphy factor. -/
theorem realWeightLift_right_holomorphic_formula (k : ℤ) (f : ℍ → ℂ)
    (g h : SL(2, ℝ)) :
    realWeightLift k f (g * h) = denom (mapGL ℝ h) I ^ (-k) *
      ((f ∣[k] (mapGL ℝ g)) ∘ ofComplex) (Complex.I + realGroupHolomorphicParameter h) := by
  rw [realWeightLift_mul, realWeightLift_apply]
  have he : Complex.I + realGroupHolomorphicParameter h = ((h • I : ℍ) : ℂ) := by
    unfold realGroupHolomorphicParameter
    abel
  rw [he, Function.comp_apply, ofComplex_apply, mul_comm]

/-- Every original real translate has exactly its genuine projective holomorphic slice and automorphy factor. -/
theorem adelicCyclicGenerator_projective_real_formula (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (h : SL(2, ℝ)) (p : AdelicProjectiveGroup) :
    adelicCyclicProjectiveFunction N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation (adelicRealSL2Embedding h)
        (adelicCyclicGenerator N f)) p =
      denom (mapGL ℝ h) I ^ (-k) *
        adelicProjectiveHolomorphicSlice N f (realGroupHolomorphicParameter h) p := by
  rw [adelicCyclicGenerator_projective_orbit_representative,
    canonicalAdelicGL2CuspLift_real_orbit, realWeightLift_right_holomorphic_formula]
  rfl

/-- The actual original real orbit in arithmetic L2 is the proved holomorphic L2 curve with its precise scalar factor. -/
theorem adelicCyclicGenerator_real_L2_formula (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (h : SL(2, ℝ))
    (hz : ‖realGroupHolomorphicParameter h‖ < (1 / 2 : ℝ)) :
    adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation (adelicRealSL2Embedding h)
        (adelicCyclicGenerator N f)) =
      denom (mapGL ℝ h) I ^ (-k) • adelicHolomorphicL2Curve N f (realGroupHolomorphicParameter h) := by
  apply Lp.ext
  filter_upwards [(adelicCyclicProjectiveFunction_memLp_two N f _).coeFn_toLp,
    Lp.coeFn_smul (denom (mapGL ℝ h) I ^ (-k))
      (adelicHolomorphicL2Curve N f (realGroupHolomorphicParameter h)),
    adelicHolomorphicL2Curve_ae_slice N f hz] with p hp hs hh
  change (adelicCyclicProjectiveFunction_memLp_two N f _).toLp _ p = _
  rw [hp, hs, Pi.smul_apply, hh]
  exact adelicCyclicGenerator_projective_real_formula N f h p

/-- The actual completed real-group generator orbit is the genuine holomorphic slice retracted to its original Hilbert space. -/
theorem adelicCyclicHilbertGenerator_real_formula {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (h : SL(2, ℝ))
    (hz : ‖realGroupHolomorphicParameter h‖ < (1 / 2 : ℝ)) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding h) (adelicCyclicHilbertGenerator f) =
      denom (mapGL ℝ h) I ^ (-k) • adelicCyclicHilbertL2Retraction f
        (adelicHolomorphicL2Curve N f (realGroupHolomorphicParameter h)) := by
  have he := congrArg (adelicCyclicHilbertL2Retraction f)
    (adelicCyclicHilbertGenerator_orbit_toL2 f (adelicRealSL2Embedding h))
  rw [adelicCyclicHilbertL2Retraction_toL2, adelicCyclicGenerator_real_L2_formula N f h hz,
    map_smul] at he
  exact he

end
end Dubon2026
