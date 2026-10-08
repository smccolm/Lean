import Dubon2026.AdelicHilbertCompactWeight

/-! # Exact real right-orbit coordinates of the original full adelic cusp function -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

/-- The genuine real special-linear group in canonical full adelic GL2. -/
def adelicRealSL2Embedding : SL(2, ℝ) →* RationalAdelicGL2 :=
  positiveAdelicGL2Embedding.comp
    (toGLPos.prod (1 : SL(2, ℝ) →* GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)))

/-- Right multiplication by an actual determinant-one real matrix preserves the rational sign correction. -/
theorem realGL2RationalSign_right_toGL (g : GeneralLinearGroup (Fin 2) ℝ) (h : SL(2, ℝ)) :
    realGL2RationalSign (g * toGL h) = realGL2RationalSign g := by
  simp [realGL2RationalSign, map_mul]

/-- The actual positive real part intertwines every original special-linear right translation. -/
theorem realGL2PositivePart_right_toGL (g : GeneralLinearGroup (Fin 2) ℝ) (h : SL(2, ℝ)) :
    realGL2PositivePart (g * toGL h) = realGL2PositivePart g * toGLPos h := by
  apply Subtype.ext
  change (rationalGL2ToReal (realGL2RationalSign (g * toGL h)))⁻¹ * (g * toGL h) =
    ((rationalGL2ToReal (realGL2RationalSign g))⁻¹ * g) * toGL h
  rw [realGL2RationalSign_right_toGL, mul_assoc]

/-- The actual real matrix selected by the original sign and strong-approximation factors. -/
def fullAdelicRealBase (N : ℕ) [NeZero N]
    (g : GeneralLinearGroup (Fin 2) ℝ)
    (x : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) : SL(2, ℝ) :=
  realPositiveNormalize
    ((rationalPositiveGL2ToReal (positiveAdelicGL2Representative N
      ((rationalGL2ToFinite (realGL2RationalSign g))⁻¹ * x)))⁻¹ * realGL2PositivePart g)

/-- Every real right orbit of the actual full function, including its negative real component, is exactly an original real lift orbit. -/
theorem fullAdelicGL2CuspLift_real_orbit (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (g : GeneralLinearGroup (Fin 2) ℝ)
    (x : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (h : SL(2, ℝ)) :
    fullAdelicGL2CuspLift N k f (g * toGL h) x =
      realWeightLift k f (fullAdelicRealBase N g x * h) := by
  unfold fullAdelicGL2CuspLift
  rw [realGL2PositivePart_right_toGL, realGL2RationalSign_right_toGL]
  unfold positiveAdelicGL2CuspLift realPositiveUnitaryLift
  rw [← mul_assoc, map_mul, realPositiveNormalize_toGLPos]
  rfl

/-- The genuine real base of a canonical adelic point uses its actual real and finite coordinates. -/
def canonicalAdelicRealBase (N : ℕ) [NeZero N] (g : RationalAdelicGL2) : SL(2, ℝ) :=
  fullAdelicRealBase N (rationalAdelicGL2RealFiniteEquiv g).1
    (rationalAdelicGL2RealFiniteEquiv g).2

/-- The original canonical adelic right orbit is precisely the original real lift at its actual base. -/
theorem canonicalAdelicGL2CuspLift_real_orbit (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (g : RationalAdelicGL2) (h : SL(2, ℝ)) :
    canonicalAdelicGL2CuspLift N k f (g * adelicRealSL2Embedding h) =
      realWeightLift k f (canonicalAdelicRealBase N g * h) := by
  have he : rationalAdelicGL2RealFiniteEquiv (adelicRealSL2Embedding h) = (toGL h, 1) :=
    rationalAdelicGL2RealFiniteEquiv.apply_symm_apply _
  unfold canonicalAdelicGL2CuspLift
  rw [map_mul, he]
  simp only [Prod.fst_mul, Prod.snd_mul, mul_one]
  exact fullAdelicGL2CuspLift_real_orbit N k f _ _ h

/-- At the actual real base, no value or normalization of the original canonical cusp function changes. -/
theorem canonicalAdelicGL2CuspLift_real_base (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (g : RationalAdelicGL2) :
    canonicalAdelicGL2CuspLift N k f g = realWeightLift k f (canonicalAdelicRealBase N g) := by
  simpa using canonicalAdelicGL2CuspLift_real_orbit N k f g 1

end
end Dubon2026
