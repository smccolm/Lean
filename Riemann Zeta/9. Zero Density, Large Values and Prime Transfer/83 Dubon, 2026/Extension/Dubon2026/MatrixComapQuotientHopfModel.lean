import Dubon2026.CoefficientComapQuotientRepresentation
import Dubon2026.MatrixFiniteCoefficientModelInvariance

/-! # Actual model equivalence along original coefficient comap quotients -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K A B ι : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing A] [CommRing B] [Fintype ι] [DecidableEq ι]

/-- When the actual target coefficient quotient is finite, an original representation has a model modulo the actual comap ideal exactly when its coefficient-changed representation has a model modulo the original target ideal. The same genuine injective quotient map and whole-representation identity prove the equivalence. -/
theorem matrixComapQuotientHopfModel_iff
    (f : A →+* B) (J : Ideal B) [Finite (B ⧸ J)]
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → A ⧸ J.comap f))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (J.comap f) ρ))) ↔
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → B ⧸ J))
      (matrixUnderlyingGroupAction
        (matrixIdealQuotientRepresentation J ((GeneralLinearGroup.map f).comp ρ)))) := by
  letI : Fintype (B ⧸ J) := Fintype.ofFinite _
  have h := matrixHopfModel_finiteCoefficient_injective_iff (R := R)
    (coefficientComapQuotientMap f J) (coefficientComapQuotientMap_injective f J)
    (matrixIdealQuotientRepresentation (J.comap f) ρ)
  rw [matrixIdealQuotientRepresentation_comap] at h
  exact h

end
end Dubon2026
