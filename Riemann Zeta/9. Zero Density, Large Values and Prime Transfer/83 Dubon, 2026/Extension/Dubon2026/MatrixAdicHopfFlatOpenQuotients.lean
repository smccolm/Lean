import Dubon2026.MatrixAdicHopfFlatCondition
import Mathlib.RingTheory.AdicCompletion.Topology

/-! # The actual all-level condition and original open coefficient quotients -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K A ι : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing A] [IsLocalRing A] [WithIdeal A] [Fintype ι] [DecidableEq ι]

/-- The actual maximal-adic neighborhood basis places a positive power inside each original open coefficient ideal. Its original level model therefore gives the original open quotient model through the genuine surjective transition. -/
theorem matrixAdicHopfFlat_openIdealModel
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (hρ : MatrixAdicHopfFlat R F K ρ) (U : Ideal A) (hU : IsOpen (U : Set A)) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ U))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation U ρ))) := by
  have hAdic : IsAdic (IsLocalRing.maximalIdeal A) := by
    rw [← hA]
    rfl
  obtain ⟨n, _hn, hnU⟩ := hAdic.hasBasis_nhds_zero.mem_iff.mp (hU.mem_nhds U.zero_mem)
  obtain ⟨m⟩ := hρ (n + 1) (Nat.zero_lt_succ n)
  exact matrixIdealQuotientHopfModel_transition_exists _ U
    ((Ideal.pow_le_pow_right (Nat.le_succ n)).trans hnU) ρ m

/-- The full positive maximal-adic condition is exactly existence of models for all original open coefficient quotients, with the original topology identified as maximal-adic. The top ideal is permitted and its quotient model follows from the same genuine quotient construction. -/
theorem matrixAdicHopfFlat_iff_openQuotients
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) :
    MatrixAdicHopfFlat R F K ρ ↔
      ∀ U : Ideal A, IsOpen (U : Set A) →
        Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ U))
          (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation U ρ))) := by
  constructor
  · exact fun hρ U hU => matrixAdicHopfFlat_openIdealModel hA ρ hρ U hU
  · intro h n _hn
    have hAdic : IsAdic (IsLocalRing.maximalIdeal A) := by
      rw [← hA]
      rfl
    exact h _ ((isAdic_iff.mp hAdic).1 n)

end
end Dubon2026
