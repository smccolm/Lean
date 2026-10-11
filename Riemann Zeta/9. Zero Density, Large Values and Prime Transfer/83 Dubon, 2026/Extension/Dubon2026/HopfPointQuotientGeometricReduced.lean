import Dubon2026.HopfPointsVanishingIdeal
import Dubon2026.LocalizedAlgebraPointInjection
import Dubon2026.FiniteReducedScalarExtension
import Mathlib.RingTheory.Localization.FractionRing

/-! # Reduced generic and geometric fibers of the actual point-coordinate quotient -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct nonZeroDivisors

variable {R F A K : Type*} [CommRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [CommRing A] [HopfAlgebra R A]
  [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]

/-- The actual quotient by vanishing on original points has reduced generic fiber: the original joint evaluation injection remains injective after clearing denominators into the same product of point-value fields. -/
theorem hopfPointQuotient_generic_isReduced
    (X : Set (WithConv (A →ₐ[R] K))) :
    IsReduced (F ⊗[R] (A ⧸ hopfPointsVanishingIdeal X)) := by
  exact localizedAlgebraPoint_isReduced R⁰ (hopfPointsQuotientEvaluation X)
    (hopfPointsQuotientEvaluation_injective X)

/-- For the original finite algebra and perfect fraction field, the literal geometric scalar extension of the actual point-coordinate quotient is reduced. No geometric reducedness or tensor faithfulness is assumed. -/
theorem hopfPointQuotient_geometric_isReduced [PerfectField F] [Module.Finite R A]
    (X : Set (WithConv (A →ₐ[R] K))) :
    IsReduced (K ⊗[R] (A ⧸ hopfPointsVanishingIdeal X)) := by
  letI := hopfPointQuotient_generic_isReduced (F := F) X
  exact finiteReducedGenericFiber_geometric_isReduced (F := F)

end
end Dubon2026
