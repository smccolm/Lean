import Dubon2026.SourceJointChartTwoChartFractions
import Dubon2026.SourceJointChartFiniteJets

/-! DUB-17/18 -> Kummer power lifting -> finite overlap. The two-chart
decomposition and finite jet isolate a bounded Laurent window. Its bound
matches the power used to move the lifted basis into the inverse chart. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial

theorem exists_two_chart_laurent_window
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] (f : F) (hf : Transcendental L f)
    (p t : L[X]) (hp : ∀ k, p.coeff k ∈ A) {d : ℕ} (ht : IsGoodAt A d t) (m : ℕ) :
    ∃ p₁ t₁ q s r : L[X], (∀ k, p₁.coeff k ∈ A) ∧ (∀ k, q.coeff k ∈ A) ∧
      (∀ k, r.coeff k ∈ A) ∧ r.natDegree ≤ m ∧ IsGood A t₁ ∧ IsGood A s ∧
      aeval f p / aeval f t = aeval f p₁ / aeval f t₁ +
        (f⁻¹) ^ m * (aeval f⁻¹ q / aeval f⁻¹ s) + aeval f⁻¹ r := by
  have hfi : Transcendental L f⁻¹ := fun h => hf (IsAlgebraic.inv_iff.mp h)
  obtain ⟨p₁, t₁, q₀, s, hp₁, hq₀, ht₁, hs, hdec⟩ :=
    exists_two_chart_fraction_decomposition A f hf p t hp ht
  obtain ⟨r, q, hr, hq, hdeg, hjet⟩ := exists_good_fraction_finite_jet A f⁻¹ hfi q₀ s hq₀ hs m
  refine ⟨p₁, t₁, q, s, r, hp₁, hq, hr, hdeg, ht₁, hs, ?_⟩
  rw [hdec, hjet]
  ring

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
