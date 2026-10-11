import Dubon2026.MatrixIdealQuotientHopfModels
import Dubon2026.MatrixConjugacyHopfModels
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # The genuine all-positive-level finite-flat model condition

This is the coordinate-model predicate underlying Conrad, Definition 1.1.1.
Defining the predicate does not establish it for any arithmetic representation.
The condition keeps every actual maximal-ideal-power reduction. The geometric
realization of finite free coordinate models is a separate proved interface.
-/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable (R F K : Type u) {ι A : Type u}
  [CommRing R] [Field F] [Field K] [Algebra R F] [Algebra F K] [Algebra R K]
  [IsScalarTower R F K] [Fintype ι] [DecidableEq ι] [CommRing A] [IsLocalRing A]

/-- Every original positive maximal-ideal-power reduction admits an actual finite free integral Hopf model with the same original Galois action. This is a condition, not an unconditional existence theorem. -/
def MatrixAdicHopfFlat (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) : Prop :=
  ∀ n : ℕ, 0 < n →
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → A ⧸ IsLocalRing.maximalIdeal A ^ n))
      (matrixUnderlyingGroupAction
        (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A ^ n) ρ)))

variable {R F K}

/-- The complete all-positive-level model condition is invariant under an actual original change of basis. Every reduced conjugator is the reduction of that same original matrix. -/
theorem matrixAdicHopfFlat_conjugacy_iff
    (ρ τ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) (U : GeneralLinearGroup ι A)
    (hc : ∀ g, τ g = U * ρ g * U⁻¹) :
    MatrixAdicHopfFlat R F K ρ ↔ MatrixAdicHopfFlat R F K τ := by
  have hlevel (n : ℕ) :
      Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
        (Multiplicative (ι → A ⧸ IsLocalRing.maximalIdeal A ^ n))
        (matrixUnderlyingGroupAction
          (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A ^ n) ρ))) ↔
      Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
        (Multiplicative (ι → A ⧸ IsLocalRing.maximalIdeal A ^ n))
        (matrixUnderlyingGroupAction
          (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A ^ n) τ))) := by
    apply matrixHopfModel_conjugacy_iff _ _
      (GeneralLinearGroup.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n)) U)
    intro g
    change GeneralLinearGroup.map _ (τ g) = _
    rw [hc g, map_mul, map_mul, map_inv]
    rfl
  exact ⟨fun h n hn => (hlevel n).mp (h n hn),
    fun h n hn => (hlevel n).mpr (h n hn)⟩

variable [IsDomain R] [IsPrincipalIdealRing R] [PerfectField F] [IsFractionRing R F]
  [Normal F K] [IsAlgClosed K]

/-- Models at a cofinal family of actual powers supply models at every positive level via genuine quotient transitions. This derives the full quantifier from the smaller cofinal family. -/
theorem matrixAdicHopfFlat_of_cofinal
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (levels : Set ℕ)
    (hlevels : ∀ n : ℕ, 0 < n → ∃ m ∈ levels, n ≤ m)
    (hmodels : ∀ m ∈ levels,
      Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
        (Multiplicative (ι → A ⧸ IsLocalRing.maximalIdeal A ^ m))
        (matrixUnderlyingGroupAction
          (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A ^ m) ρ)))) :
    MatrixAdicHopfFlat R F K ρ := by
  intro n hn
  obtain ⟨m, hm, hnm⟩ := hlevels n hn
  obtain ⟨model⟩ := hmodels m hm
  exact matrixIdealQuotientHopfModel_transition_exists _ _
    (Ideal.pow_le_pow_right hnm) ρ model

end
end Dubon2026
