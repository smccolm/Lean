import Dubon2026.SourceIntegralGenericFibreAction
import Dubon2026.SourceInducedGroupIrreducible
import Dubon2026.CMSourceIntegralWeight

/-! Original irreducible generic fibres for the actual source embedding factors.
Each factor in the same arithmetic coefficient tensor is the literal
integral induced module. Its original generic fibre is identified with
the actual irreducible highest-weight representation, preserving the
normalized vector and every original integral matrix action.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField ValuativeRel TensorProduct

/-- Each actual source embedding factor has its original irreducible highest-weight generic fibre, with the integral action and normalized highest vector preserved by the constructed comparison. -/
theorem cmSourceIntegralWeight_factor_identification
    (K E : Type) [Field K] [NumberField K] [Field E] [CharZero E]
    (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
    [ValuativeRel E]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]
    (places : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (lam : IntegralCoefficientEmbeddingIndex K E p hp places → Fin (n + 1) → ℤ)
    (hlam : ∀ i, Antitone (lam i))
    (i : IntegralCoefficientEmbeddingIndex K E p hp places) :
    ∃ e : E ⊗[𝒪[E]] generalLinearIntegralInducedSubmodule 𝒪[E] (n + 1) (lam i) ≃ₗ[E]
        generalLinearIntegralInducedSubmodule E (n + 1) (lam i),
      Representation.IsIrreducible (generalLinearIntegralInducedRepresentation E (n + 1) (lam i)) ∧
      e ((1 : E) ⊗ₜ[𝒪[E]] integralDominantHighestVector 𝒪[E] (lam i) (hlam i)) =
        integralDominantHighestVector E (lam i) (hlam i) ∧
      ∀ (g : Matrix.GeneralLinearGroup (Fin (n + 1)) 𝒪[E])
        (z : E ⊗[𝒪[E]] generalLinearIntegralInducedSubmodule 𝒪[E] (n + 1) (lam i)),
        e ((generalLinearIntegralInducedRepresentation 𝒪[E] (n + 1) (lam i) g).baseChange E z) =
          generalLinearIntegralInducedRepresentation E (n + 1) (lam i)
            (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[E] E) g) (e z) := by
  refine ⟨sourceIntegralGenericFibreEquiv 𝒪[E] E (lam i) (hlam i),
    sourceInduced_isIrreducible E (lam i) (hlam i),
    sourceIntegralGenericFibreEquiv_highest 𝒪[E] E (lam i) (hlam i), ?_⟩
  exact sourceIntegralGenericFibreEquiv_action 𝒪[E] E (lam i) (hlam i)

end
end Dubon2026
