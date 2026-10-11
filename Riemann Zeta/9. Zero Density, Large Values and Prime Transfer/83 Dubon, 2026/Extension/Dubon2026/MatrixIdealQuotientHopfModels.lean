import Dubon2026.MatrixCoefficientHopfModels
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Flat.Localization

/-! # Genuine Hopf models under original ideal-quotient transitions -/

namespace Dubon2026
noncomputable section

universe uC
open Matrix

variable {G ι A : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing A]

/-- Reduce precisely the original whole matrix representation modulo the given actual coefficient ideal. -/
def matrixIdealQuotientRepresentation (I : Ideal A)
    (ρ : G →* GeneralLinearGroup ι A) : G →* GeneralLinearGroup ι (A ⧸ I) :=
  (GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp ρ

/-- The actual original ideal-quotient transition gives exactly the representation at the larger ideal. -/
theorem matrixIdealQuotientRepresentation_transition (I J : Ideal A) (hIJ : I ≤ J)
    (ρ : G →* GeneralLinearGroup ι A) :
    (GeneralLinearGroup.map (Ideal.Quotient.factor hIJ)).comp
      (matrixIdealQuotientRepresentation I ρ) = matrixIdealQuotientRepresentation J ρ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  ext i j
  rfl

variable {R F K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]

/-- A model at the original finer coefficient ideal gives a genuine model at every coarser ideal, through the actual surjective quotient transition. -/
def matrixIdealQuotientHopfModelTransition (I J : Ideal A) (hIJ : I ≤ J)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A ⧸ I))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I ρ))) :
    FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A ⧸ J))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation J ρ)) := by
  letI : Module.Flat R F := IsLocalization.flat F (nonZeroDivisors R)
  letI : Module.Flat R K := Module.Flat.trans R F K
  have E := matrixIdealQuotientRepresentation_transition I J hIJ ρ
  rw [← E]
  exact matrixCoefficientHopfModelOfSurjective (Ideal.Quotient.factor hIJ)
    (Ideal.Quotient.factor_surjective hIJ) (matrixIdealQuotientRepresentation I ρ) m

/-- Existence at the original finer ideal derives existence at the coarser ideal without assuming the latter model. -/
theorem matrixIdealQuotientHopfModel_transition_exists (I J : Ideal A) (hIJ : I ≤ J)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A ⧸ I))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I ρ))) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A ⧸ J))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation J ρ))) := by
  exact ⟨matrixIdealQuotientHopfModelTransition I J hIJ ρ m⟩

end
end Dubon2026
