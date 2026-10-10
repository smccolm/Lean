import Dubon2026.ClosedProfiniteQuotients
import Dubon2026.FixedResidualTopologicalGeneration
import Dubon2026.ProfiniteGeneratorPresentations

/-! # Actual profinite presentation of the entire original fixed residual quotient -/

namespace Dubon2026

noncomputable section

/-- Original residual character finiteness gives a genuine surjective profinite presentation of the entire fixed ambient quotient on actual finitely many generators. -/
theorem fixedResidualProfiniteQuotient_has_presentation
    (p : ℕ) (hp : p.Prime) (G : ProfiniteGrp) (K : Subgroup G) [K.Normal]
    [Finite (G ⧸ K)] (hK : IsClosed (K : Set G))
    [Finite (K →ₜ* Multiplicative (ZMod p))] :
    ∃ S : Finset (fixedResidualProfiniteQuotient p G K hK),
      Function.Surjective (profiniteGeneratorPresentation
        (fixedResidualProfiniteQuotient p G K hK) S) := by
  obtain ⟨S, hS⟩ := fixedResidualQuotient_finitely_generated p hp G K hK
  exact ⟨S, profiniteGeneratorPresentation_surjective
    (fixedResidualProfiniteQuotient p G K hK) S hS⟩

end
end Dubon2026
