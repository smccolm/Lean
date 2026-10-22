import Dubon2026.SourceOriginalPeriodExponential

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
global meromorphic exponential. The actual divisor supplies a base point and
all avoiding paths, so an integral-period original differential yields a
function nonzero off its support with exact exponential transport. The next
step must prove this function meromorphic with the prescribed orders.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_period_exponential (D : Divisor ℂ F) (η : Ω[F⁄ℂ])
    (hη : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ F) (α : Path P P), (∀ t, D (α t) = 0) →
      ∃ m : ℤ, pathIntegral N η α = 2 * Real.pi * Complex.I * m) :
    ∃ g : Place ℂ F → ℂ, (∀ P, D P = 0 → g P ≠ 0) ∧
      ∀ (P Q : Place ℂ F) (σ : Path P Q), D P = 0 → D Q = 0 →
        (∀ t, D (σ t) = 0) → g Q = g P * Complex.exp (pathIntegral N η σ) := by
  obtain ⟨P₀, hP₀⟩ := exists_original_divisor_base_point N D
  refine ⟨originalPeriodExponential N D η P₀ hP₀,
    originalPeriodExponential_ne_zero N D η P₀ hP₀, ?_⟩
  intro P Q σ hP hQ hσ
  exact originalPeriodExponential_transport N D η hη hres hper P₀ hP₀ P Q hP hQ σ hσ

end
end Dubon2026.SourceFunctionField.OriginalChart
