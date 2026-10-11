import Dubon2026.MatrixHopfModelCoefficientIdeal
import Mathlib.RingTheory.LocalRing.Quotient

/-! # A genuine residual model makes the original model coefficient quotient local -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K A ι : Type u} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [CommRing A] [IsLocalRing A] [TopologicalSpace A] [Fintype ι] [DecidableEq ι]

/-- An actual model of the original residual representation places its original coefficient maximal ideal in the literal model family, so the model coefficient ideal lies inside that same maximal ideal. -/
theorem matrixHopfModelCoefficientIdeal_le_maximal
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (hopen : IsOpen (IsLocalRing.maximalIdeal A : Set A))
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → A ⧸ IsLocalRing.maximalIdeal A))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A) ρ))) :
    matrixHopfModelCoefficientIdeal R F K ρ ≤ IsLocalRing.maximalIdeal A := by
  exact iInf_le (fun I : {I : Ideal A // I ∈ matrixHopfModelIdealFamily R F K ρ} => I.val)
    ⟨IsLocalRing.maximalIdeal A, hopen, ⟨m⟩⟩

/-- The actual model coefficient quotient is a nontrivial local ring when the same original residual representation has a genuine model. Properness follows from the actual maximal ideal, and locality from the original surjective quotient map. -/
theorem matrixHopfModelCoefficientQuotient_isLocal
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (hopen : IsOpen (IsLocalRing.maximalIdeal A : Set A))
    (m : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → A ⧸ IsLocalRing.maximalIdeal A))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A) ρ))) :
    IsLocalRing (A ⧸ matrixHopfModelCoefficientIdeal R F K ρ) := by
  have hproper : matrixHopfModelCoefficientIdeal R F K ρ ≠ ⊤ := by
    intro ht
    have hm := matrixHopfModelCoefficientIdeal_le_maximal ρ hopen m
    rw [ht, top_le_iff] at hm
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top hm
  letI : Nontrivial (A ⧸ matrixHopfModelCoefficientIdeal R F K ρ) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  exact IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (matrixHopfModelCoefficientIdeal R F K ρ)) Ideal.Quotient.mk_surjective

end
end Dubon2026
