import Dubon2026.HopfPointsVanishingIdeal
import Mathlib.Algebra.Module.Torsion.Pi
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Finiteness.Quotient

/-! # Torsion-free and finite free coordinates of the actual point closure -/

namespace Dubon2026
noncomputable section

variable {R A K : Type*} [CommRing R] [IsDomain R] [CommRing A] [HopfAlgebra R A]
  [Field K] [Algebra R K] [FaithfulSMul R K]

/-- The actual point-closure coordinate quotient is torsion-free over the original base because its genuine evaluation embeds it into a product of faithful field algebras. -/
theorem hopfPointsCoordinateQuotient_isTorsionFree
    (X : Set (WithConv (A →ₐ[R] K))) :
    Module.IsTorsionFree R (A ⧸ hopfPointsVanishingIdeal X) := by
  exact (hopfPointsQuotientEvaluation_injective X).moduleIsTorsionFree _
    (fun r a => (hopfPointsQuotientEvaluation X).toLinearMap.map_smul r a)

/-- Over a principal ideal domain, a finite original coordinate algebra gives a finite free actual point-closure quotient. This proves its module structure without assuming flatness of that quotient. -/
theorem hopfPointsCoordinateQuotient_finite_free [IsPrincipalIdealRing R] [Module.Finite R A]
    (X : Set (WithConv (A →ₐ[R] K))) :
    Module.Finite R (A ⧸ hopfPointsVanishingIdeal X) ∧
      Module.Free R (A ⧸ hopfPointsVanishingIdeal X) := by
  letI := hopfPointsCoordinateQuotient_isTorsionFree X
  exact ⟨inferInstance, inferInstance⟩

end
end Dubon2026
