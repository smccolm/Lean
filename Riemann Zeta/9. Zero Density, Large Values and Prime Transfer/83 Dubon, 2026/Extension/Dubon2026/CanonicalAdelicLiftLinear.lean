import Dubon2026.AdelicHeckeClassicalReconstruction

/-! # Complex linearity of the actual original full adelic lift -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane

/-- The original full adelic lift, with its literal sign and strong-approximation choices, is complex linear in the original classical function. -/
def canonicalAdelicGL2CuspLiftLinear (N : ℕ) [NeZero N] (k : ℤ) :
    (ℍ → ℂ) →ₗ[ℂ] (RationalAdelicGL2 → ℂ) where
  toFun := canonicalAdelicGL2CuspLift N k
  map_add' F G := by
    funext a
    exact congrFun ((realWeightLiftLinear k).map_add F G)
      (fullAdelicRealBase N (rationalAdelicGL2RealFiniteEquiv a).1 (rationalAdelicGL2RealFiniteEquiv a).2)
  map_smul' c F := by
    funext a
    exact congrFun ((realWeightLiftLinear k).map_smul c F)
      (fullAdelicRealBase N (rationalAdelicGL2RealFiniteEquiv a).1 (rationalAdelicGL2RealFiniteEquiv a).2)

/-- Scalar multiplication of the actual original classical function gives exactly scalar multiplication of its full adelic lift. -/
theorem canonicalAdelicGL2CuspLift_smul (N : ℕ) [NeZero N] (k : ℤ) (c : ℂ) (F : ℍ → ℂ) :
    canonicalAdelicGL2CuspLift N k (c • F) = c • canonicalAdelicGL2CuspLift N k F :=
  (canonicalAdelicGL2CuspLiftLinear N k).map_smul c F

end
end Dubon2026
