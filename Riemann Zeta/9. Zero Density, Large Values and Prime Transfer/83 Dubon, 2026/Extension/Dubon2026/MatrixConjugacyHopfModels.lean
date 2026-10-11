import Dubon2026.MatrixConjugacyVectorEquiv
import Dubon2026.FiniteFreeHopfPointModelEquiv

/-! # Genuine Hopf model invariance under original matrix conjugacy -/

namespace Dubon2026
noncomputable section

universe uC
open Matrix

variable {R F K ι A : Type*} [CommRing R] [Field F] [Field K]
  [Algebra R F] [Algebra F K] [Algebra R K] [IsScalarTower R F K]
  [Fintype ι] [DecidableEq ι] [CommRing A]

/-- A genuine change of basis transports the original model with exactly the same integral Hopf coordinates. -/
def matrixHopfModelOfConjugacy
    (ρ τ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) (U : GeneralLinearGroup ι A)
    (hc : ∀ g, τ g = U * ρ g * U⁻¹)
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ)) :
    FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction τ) :=
  finiteFreeHopfPointModelEquiv m (matrixConjugacyVectorEquiv U)
    (matrixConjugacyVectorEquiv_equivariant ρ τ U hc)

/-- The existence of an actual finite free Hopf model is unchanged by the original whole matrix conjugacy. -/
theorem matrixHopfModel_conjugacy_iff
    (ρ τ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) (U : GeneralLinearGroup ι A)
    (hc : ∀ g, τ g = U * ρ g * U⁻¹) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ)) ↔
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction τ)) := by
  constructor
  · rintro ⟨m⟩
    exact ⟨matrixHopfModelOfConjugacy ρ τ U hc m⟩
  · rintro ⟨m⟩
    refine ⟨matrixHopfModelOfConjugacy τ ρ U⁻¹ ?_ m⟩
    intro g
    rw [hc g]
    simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

/-- Strict conjugacy of the original representation preserves actual Hopf model existence; its residue requirement is used only to specify that original equivalence relation. -/
theorem matrixHopfModel_strictConjugacy_iff {k : Type*} [CommRing k]
    (r : A →+* k) (ρ τ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (h : MatrixStrictlyConjugate r ρ τ) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ)) ↔
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction τ)) := by
  obtain ⟨U, _, hc⟩ := h
  exact matrixHopfModel_conjugacy_iff ρ τ U hc

end
end Dubon2026
