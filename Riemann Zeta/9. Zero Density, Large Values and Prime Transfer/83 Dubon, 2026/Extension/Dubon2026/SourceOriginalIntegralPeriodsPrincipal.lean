import Dubon2026.SourceOriginalExponentialMeromorphicOrders
import Dubon2026.SourceOriginalMeromorphicPrincipalDivisor

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse.
An original simple-pole differential with prescribed divisor residues and
integral loop periods produces a meromorphic exponential of the exact orders,
and the proved original-function comparison makes the divisor principal.
The integral-period correction and reciprocity theorems remain required.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_meromorphic_orders_of_integral_periods
    (D : Divisor ℂ F) (η : Ω[F⁄ℂ])
    (hη : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ F) (α : Path P P), (∀ t, D (α t) = 0) →
      ∃ m : ℤ, pathIntegral N η α = 2 * Real.pi * Complex.I * m) :
    ∃ g : Place ℂ F → ℂ, ∀ v, MeromorphicAt (fun z => g (placeFamily N v z)) 0 ∧
      meromorphicOrderAt (fun z => g (placeFamily N v z)) 0 = (D v : WithTop ℤ) := by
  obtain ⟨g, hgn, ht⟩ := exists_original_period_exponential N D η hη hres hper
  exact ⟨g, original_meromorphic_orders_of_exponential_transport N D η hη hres g hgn ht⟩

theorem original_isPrincipal_of_integral_periods
    (D : Divisor ℂ F) (η : Ω[F⁄ℂ])
    (hη : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (hper : ∀ (P : Place ℂ F) (α : Path P P), (∀ t, D (α t) = 0) →
      ∃ m : ℤ, pathIntegral N η α = 2 * Real.pi * Complex.I * m) :
    Divisor.IsPrincipal D := by
  obtain ⟨g, hg⟩ := exists_original_meromorphic_orders_of_integral_periods N D η hη hres hper
  exact original_isPrincipal_of_meromorphic_orders N D g (fun v => (hg v).1) (fun v => (hg v).2)

end
end Dubon2026.SourceFunctionField.OriginalChart
