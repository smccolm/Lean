import Dubon2026.AdelicGeneratorDerivativeRepresentatives
import Dubon2026.AdelicHilbertGeneratorDerivatives

/-! # The actual holomorphic infinitesimal identity in the original quotient L2 space -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

/-- The projective pointwise derivatives retain exactly the original holomorphic weight identity. -/
theorem adelicProjectiveRealOrbit_holomorphic_identity (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (p : AdelicProjectiveGroup) :
    deriv (fun t : ℝ => adelicProjectiveRealOrbit N f realGeodesicCurve t p) 0 -
      Complex.I * deriv (fun t : ℝ => adelicProjectiveRealOrbit N f realUpperUnipotent t p) 0 =
      (k : ℂ) / 2 * adelicCyclicProjectiveFunction N f (adelicCyclicGenerator N f) p := by
  obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective p.1
  obtain ⟨a, ha⟩ := ProjGenLinGroup.mk_surjective p.2
  have hp : p = (QuotientGroup.mk r, ProjGenLinGroup.mk a) := Prod.ext hr.symm ha.symm
  rw [hp]
  exact canonicalAdelicGL2CuspLift_holomorphic_infinitesimal N f
    (rationalAdelicGL2RealFiniteEquiv.symm (toGL r, a))

/-- The genuine L2 derivatives of the original cusp generator satisfy the actual holomorphic infinitesimal identity. -/
theorem adelicCyclicGenerator_L2_holomorphic_identity (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    deriv (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicGenerator N f))) 0 -
    Complex.I • deriv (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicGenerator N f))) 0 =
    ((k : ℂ) / 2) • adelicProjectiveCyclicToL2 N f (adelicCyclicGenerator N f) := by
  let A := deriv (fun t : ℝ => adelicProjectiveCyclicToL2 N f
    ((adelicLiftCyclicRepresentation N k f).toRepresentation
      (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicGenerator N f))) 0
  let U := deriv (fun t : ℝ => adelicProjectiveCyclicToL2 N f
    ((adelicLiftCyclicRepresentation N k f).toRepresentation
      (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicGenerator N f))) 0
  let v := adelicProjectiveCyclicToL2 N f (adelicCyclicGenerator N f)
  change A - Complex.I • U = ((k : ℂ) / 2) • v
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub A (Complex.I • U), Lp.coeFn_smul Complex.I U,
    Lp.coeFn_smul ((k : ℂ) / 2) v,
    adelicCyclicGenerator_geodesic_L2_deriv_ae N f,
    adelicCyclicGenerator_unipotent_L2_deriv_ae N f,
    (adelicCyclicProjectiveFunction_memLp_two N f (adelicCyclicGenerator N f)).coeFn_toLp]
    with p hsub hsmul hweight hA hU hv
  rw [hsub, hweight]
  change A p - (Complex.I • U) p = ((k : ℂ) / 2) * v p
  rw [hsmul]
  change A p - Complex.I * U p = ((k : ℂ) / 2) * v p
  exact (congrArg₂ (fun x y : ℂ => x - Complex.I * y) hA hU).trans
    ((adelicProjectiveRealOrbit_holomorphic_identity N f p).trans
      (congrArg (fun x : ℂ => ((k : ℂ) / 2) * x) hv.symm))

end
end Dubon2026
