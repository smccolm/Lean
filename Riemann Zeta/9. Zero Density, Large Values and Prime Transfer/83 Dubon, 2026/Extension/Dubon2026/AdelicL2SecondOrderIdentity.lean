import Dubon2026.AdelicOrbitJetIdentification
import Dubon2026.AdelicLiftCasimir

/-! # The original second-order differential relation in actual arithmetic L2 -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

/-- The original pointwise projective orbit jets have the exact original holomorphic second-order relation. -/
theorem adelicProjectiveRealOrbit_second_order_identity (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (p : AdelicProjectiveGroup) :
    iteratedDeriv 2 (fun t : ℝ => adelicProjectiveRealOrbit N f realGeodesicCurve t p) 0 -
      iteratedDeriv 1 (fun t : ℝ => adelicProjectiveRealOrbit N f realGeodesicCurve t p) 0 +
      iteratedDeriv 2 (fun t : ℝ => adelicProjectiveRealOrbit N f realUpperUnipotent t p) 0 -
      (k : ℂ) * Complex.I *
        iteratedDeriv 1 (fun t : ℝ => adelicProjectiveRealOrbit N f realUpperUnipotent t p) 0 =
      ((k : ℂ) / 2) * ((k : ℂ) / 2 - 1) *
        adelicCyclicProjectiveFunction N f (adelicCyclicGenerator N f) p := by
  simp_rw [adelicProjectiveRealOrbit_representative_eq, canonicalAdelicGL2CuspLift_real_orbit]
  rw [adelicCyclicProjectiveFunction_representative]
  change _ = ((k : ℂ) / 2) * ((k : ℂ) / 2 - 1) *
    canonicalAdelicGL2CuspLift N k f (adelicProjectiveRepresentative p)
  rw [canonicalAdelicGL2CuspLift_real_base]
  have he := realWeightLift_second_order_identity k (ModularFormClass.holo f)
    (canonicalAdelicRealBase N (adelicProjectiveRepresentative p))
  rw [realRightDerivative_twice _ realGeodesicCurve_add,
    realRightDerivative_twice _ realUpperUnipotent_add] at he
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, realRightDerivative] using he

/-- The original quotient L2 jets satisfy the genuine weight-restricted second-order identity. -/
theorem adelicCyclicGenerator_L2_second_order_identity (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    iteratedDeriv 2 (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicGenerator N f))) 0 -
    iteratedDeriv 1 (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicGenerator N f))) 0 +
    iteratedDeriv 2 (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicGenerator N f))) 0 -
    ((k : ℂ) * Complex.I) • iteratedDeriv 1 (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicGenerator N f))) 0 =
      (((k : ℂ) / 2) * ((k : ℂ) / 2 - 1)) • adelicProjectiveCyclicToL2 N f (adelicCyclicGenerator N f) := by
  let A := fun t : ℝ => adelicProjectiveCyclicToL2 N f
    ((adelicLiftCyclicRepresentation N k f).toRepresentation
      (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicGenerator N f))
  let U := fun t : ℝ => adelicProjectiveCyclicToL2 N f
    ((adelicLiftCyclicRepresentation N k f).toRepresentation
      (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicGenerator N f))
  let A₂ := iteratedDeriv 2 A 0
  let A₁ := iteratedDeriv 1 A 0
  let U₂ := iteratedDeriv 2 U 0
  let U₁ := iteratedDeriv 1 U 0
  let v := adelicProjectiveCyclicToL2 N f (adelicCyclicGenerator N f)
  let b : ℂ := k * Complex.I
  let a : ℂ := (k / 2) * (k / 2 - 1)
  change A₂ - A₁ + U₂ - b • U₁ = a • v
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (A₂ - A₁ + U₂) (b • U₁),
    Lp.coeFn_add (A₂ - A₁) U₂, Lp.coeFn_sub A₂ A₁,
    Lp.coeFn_smul b U₁, Lp.coeFn_smul a v,
    adelicCyclicGenerator_geodesic_L2_jets_ae N f 2 0,
    adelicCyclicGenerator_geodesic_L2_jets_ae N f 1 0,
    adelicCyclicGenerator_unipotent_L2_jets_ae N f 2 0,
    adelicCyclicGenerator_unipotent_L2_jets_ae N f 1 0,
    (adelicCyclicProjectiveFunction_memLp_two N f (adelicCyclicGenerator N f)).coeFn_toLp]
    with p hsub hadd hdiff hsmul hweight hA₂ hA₁ hU₂ hU₁ hv
  rw [hsub, Pi.sub_apply, hadd, Pi.add_apply, hdiff, Pi.sub_apply,
    hsmul, Pi.smul_apply, hweight, Pi.smul_apply]
  change A₂ p - A₁ p + U₂ p - b * U₁ p = a * v p
  change v p = adelicCyclicProjectiveFunction N f (adelicCyclicGenerator N f) p at hv
  rw [hA₂, hA₁, hU₂, hU₁, hv]
  exact adelicProjectiveRealOrbit_second_order_identity N f p

end
end Dubon2026
