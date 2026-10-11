import Dubon2026.FiniteCoefficientExtensionHopfModel
import Dubon2026.MatrixAdicHopfFlatFiniteCoefficients

/-! # Actual finite coefficient inclusions preserve and reflect model existence -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K A B ι : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing A] [CommRing B] [Fintype B] [Fintype ι] [DecidableEq ι]

/-- Along an actual inclusion into finite original coefficients, the original matrix representation has a genuine model exactly when its actual coefficient extension does. The forward direction uses the genuine finite product spanning quotient; the reverse direction uses the actual vector-group embedding. -/
theorem matrixHopfModel_finiteCoefficient_injective_iff
    (f : A →+* B) (hf : Function.Injective f)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ)) ↔
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → B))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map f).comp ρ))) := by
  constructor
  · rintro ⟨m⟩
    exact finiteCoefficientExtensionHopfModel_exists f ρ m
  · rintro ⟨m⟩
    exact matrixCoefficientHopfModel_of_injective_exists f hf ρ m

variable [IsLocalRing A] [IsLocalRing B]

/-- For actual finite local coefficients, the same original coefficient inclusion preserves and reflects the complete positive-level condition. Source finiteness is derived from the actual injection; original local nilpotence identifies both all-level conditions with their genuine full model conditions. -/
theorem matrixAdicHopfFlat_finiteCoefficient_injective_iff
    (f : A →+* B) (hf : Function.Injective f)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) :
    MatrixAdicHopfFlat R F K ρ ↔
      MatrixAdicHopfFlat R F K ((GeneralLinearGroup.map f).comp ρ) := by
  letI : Finite A := Finite.of_injective f hf
  rw [matrixAdicHopfFlat_finite_iff, matrixAdicHopfFlat_finite_iff]
  exact matrixHopfModel_finiteCoefficient_injective_iff f hf ρ

end
end Dubon2026
