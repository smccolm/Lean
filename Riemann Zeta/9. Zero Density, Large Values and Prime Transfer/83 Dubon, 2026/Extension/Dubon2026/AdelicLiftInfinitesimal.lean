import Dubon2026.AdelicRealOrbitCoordinates
import Dubon2026.RealLiftInfinitesimal

/-! # The genuine holomorphic infinitesimal identity at every original adelic point -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

/-- The actual complex derivative of the original slash transform selected by an adelic point. -/
def canonicalAdelicHolomorphicDerivative (N : ℕ) [NeZero N] (k : ℤ)
    (f : ℍ → ℂ) (g : RationalAdelicGL2) : ℂ :=
  deriv ((f ∣[k] (mapGL ℝ (canonicalAdelicRealBase N g))) ∘ ofComplex) Complex.I

/-- The original canonical cusp function has its genuine unipotent derivative at every adelic point. -/
theorem canonicalAdelicGL2CuspLift_unipotent_hasDerivAt (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : RationalAdelicGL2) :
    HasDerivAt (fun t : ℝ => canonicalAdelicGL2CuspLift N k f
      (g * adelicRealSL2Embedding (realUpperUnipotent t)))
      (canonicalAdelicHolomorphicDerivative N k f g) 0 := by
  simp_rw [canonicalAdelicGL2CuspLift_real_orbit]
  exact realWeightLift_right_unipotent_hasDerivAt k (ModularFormClass.holo f) _

/-- The actual geodesic derivative of the original full adelic cusp function retains its precise weight term. -/
theorem canonicalAdelicGL2CuspLift_geodesic_hasDerivAt (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : RationalAdelicGL2) :
    HasDerivAt (fun t : ℝ => canonicalAdelicGL2CuspLift N k f
      (g * adelicRealSL2Embedding (realGeodesicCurve t)))
      ((k : ℂ) / 2 * canonicalAdelicGL2CuspLift N k f g +
        Complex.I * canonicalAdelicHolomorphicDerivative N k f g) 0 := by
  simp_rw [canonicalAdelicGL2CuspLift_real_orbit]
  rw [canonicalAdelicGL2CuspLift_real_base]
  exact realWeightLift_right_geodesic_hasDerivAt k (ModularFormClass.holo f) _

/-- The original canonical adelic function satisfies the exact first-order holomorphic identity without an infinitesimal premise. -/
theorem canonicalAdelicGL2CuspLift_holomorphic_infinitesimal (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : RationalAdelicGL2) :
    deriv (fun t : ℝ => canonicalAdelicGL2CuspLift N k f
      (g * adelicRealSL2Embedding (realGeodesicCurve t))) 0 -
      Complex.I * deriv (fun t : ℝ => canonicalAdelicGL2CuspLift N k f
        (g * adelicRealSL2Embedding (realUpperUnipotent t))) 0 =
        (k : ℂ) / 2 * canonicalAdelicGL2CuspLift N k f g := by
  rw [(canonicalAdelicGL2CuspLift_geodesic_hasDerivAt N f g).deriv,
    (canonicalAdelicGL2CuspLift_unipotent_hasDerivAt N f g).deriv]
  ring

/-- The literal right representation on the original algebraic generator consumes the proved pointwise holomorphic identity. -/
theorem adelicCyclicGenerator_holomorphic_infinitesimal (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : RationalAdelicGL2) :
    deriv (fun t : ℝ => ((adelicLiftCyclicRepresentation N k f).toRepresentation
      (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicGenerator N f)).val g) 0 -
      Complex.I * deriv (fun t : ℝ => ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicGenerator N f)).val g) 0 =
          (k : ℂ) / 2 * (adelicCyclicGenerator N f).val g :=
  canonicalAdelicGL2CuspLift_holomorphic_infinitesimal N f g

end
end Dubon2026
