import Dubon2026.AdelicLiftInfinitesimal
import Dubon2026.RealLiftCasimir

/-! # Exact original full adelic second-order differential eigenvalue -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- The actual selected real base intertwines every original special-linear right translation. -/
theorem fullAdelicRealBase_right (N : ℕ) [NeZero N]
    (g : GeneralLinearGroup (Fin 2) ℝ)
    (x : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (h : SL(2, ℝ)) :
    fullAdelicRealBase N (g * toGL h) x = fullAdelicRealBase N g x * h := by
  unfold fullAdelicRealBase
  rw [realGL2RationalSign_right_toGL, realGL2PositivePart_right_toGL,
    ← mul_assoc, map_mul, realPositiveNormalize_toGLPos]

/-- At canonical full adelic points, the genuine real base retains its exact right-equivariance. -/
theorem canonicalAdelicRealBase_right (N : ℕ) [NeZero N]
    (g : RationalAdelicGL2) (h : SL(2, ℝ)) :
    canonicalAdelicRealBase N (g * adelicRealSL2Embedding h) = canonicalAdelicRealBase N g * h := by
  have he : rationalAdelicGL2RealFiniteEquiv (adelicRealSL2Embedding h) = (toGL h, 1) :=
    rationalAdelicGL2RealFiniteEquiv.apply_symm_apply _
  unfold canonicalAdelicRealBase
  rw [map_mul, he]
  simp only [Prod.fst_mul, Prod.snd_mul, mul_one]
  exact fullAdelicRealBase_right N _ _ h

/-- The actual pointwise right derivative along the embedded real curve in full adelic GL2. -/
def adelicRightDerivative (c : ℝ → SL(2, ℝ)) (F : RationalAdelicGL2 → ℂ)
    (g : RationalAdelicGL2) : ℂ :=
  deriv (fun t : ℝ => F (g * adelicRealSL2Embedding (c t))) 0

/-- Exact real-base equivariance transports the literal adelic derivative to the original real derivative. -/
theorem adelicRightDerivative_realBase (N : ℕ) [NeZero N] (c : ℝ → SL(2, ℝ))
    (Φ : SL(2, ℝ) → ℂ) (g : RationalAdelicGL2) :
    adelicRightDerivative c (fun h => Φ (canonicalAdelicRealBase N h)) g =
      realRightDerivative c Φ (canonicalAdelicRealBase N g) := by
  simp only [adelicRightDerivative, realRightDerivative, canonicalAdelicRealBase_right]

/-- The genuine adelic second-order operator uses the original embedded geodesic, unipotent and compact curves. -/
def adelicCasimirOperator (F : RationalAdelicGL2 → ℂ) (g : RationalAdelicGL2) : ℂ :=
  -adelicRightDerivative realGeodesicCurve (adelicRightDerivative realGeodesicCurve F) g +
    adelicRightDerivative realGeodesicCurve F g -
    adelicRightDerivative realUpperUnipotent (adelicRightDerivative realUpperUnipotent F) g +
    adelicRightDerivative realUpperUnipotent (adelicRightDerivative realRotationCurve F) g

/-- The actual full adelic second-order operator is exactly the original real operator in the genuine real-base coordinates. -/
theorem adelicCasimirOperator_realBase (N : ℕ) [NeZero N] (Φ : SL(2, ℝ) → ℂ)
    (g : RationalAdelicGL2) :
    adelicCasimirOperator (fun h => Φ (canonicalAdelicRealBase N h)) g =
      realCasimirOperator Φ (canonicalAdelicRealBase N g) := by
  simp only [adelicCasimirOperator, realCasimirOperator, adelicRightDerivative,
    realRightDerivative, canonicalAdelicRealBase_right]

/-- The original canonical adelic cusp function has its precise second-order differential eigenvalue at every full adelic point. -/
theorem canonicalAdelicGL2CuspLift_casimir (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : RationalAdelicGL2) :
    adelicCasimirOperator (canonicalAdelicGL2CuspLift N k f) g =
      ((k : ℂ) / 2) * (1 - (k : ℂ) / 2) * canonicalAdelicGL2CuspLift N k f g := by
  have he : canonicalAdelicGL2CuspLift N k f =
      fun h => realWeightLift k f (canonicalAdelicRealBase N h) :=
    funext (canonicalAdelicGL2CuspLift_real_base N k f)
  rw [he, adelicCasimirOperator_realBase]
  exact realWeightLift_casimir k (ModularFormClass.holo f) _

/-- The genuine algebraic cyclic generator consumes the original full adelic differential eigenvalue. -/
theorem adelicCyclicGenerator_casimir (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (g : RationalAdelicGL2) :
    adelicCasimirOperator (adelicCyclicGenerator N f).val g =
      ((k : ℂ) / 2) * (1 - (k : ℂ) / 2) * (adelicCyclicGenerator N f).val g :=
  canonicalAdelicGL2CuspLift_casimir N f g

end
end Dubon2026
