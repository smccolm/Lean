import Dubon2026.SourceOriginalRamifiedRegularOrder
import Dubon2026.SourceOriginalPlaceInverseValues

/-! DUB-17/18 -> original torsion cardinality -> complex place charts.
The original residue-value function is meromorphic on the descended
family for every original rational function, including poles. Inversion
reduces the pole case to the proved regular case. Every nonzero function
has exactly its original normalized order, with no ramification factor
and no supplied analytic realization or order-comparison hypothesis.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane

theorem meromorphicAt_originalRamifiedPlace_eval (N : ℕ) [NeZero N] (τ : ℍ)
    (f : modularFunctionFieldOver N ℂ) :
    MeromorphicAt (fun z => originalPlaceEval N ℂ (originalRamifiedPlace N τ z) f) 0 := by
  by_cases hf : f ∈ (originalAnalyticPlace N τ).toValuationSubring
  · exact (originalRamifiedPlace_regular_analytic N τ f hf).1.meromorphicAt
  · have hi : f⁻¹ ∈ (originalAnalyticPlace N τ).toValuationSubring :=
      ((originalAnalyticPlace N τ).toValuationSubring.mem_or_inv_mem f).resolve_left hf
    have h := (originalRamifiedPlace_regular_analytic N τ f⁻¹ hi).1.meromorphicAt.inv
    simp only [originalPlaceEval_inv] at h
    change MeromorphicAt (((fun z => originalPlaceEval N ℂ (originalRamifiedPlace N τ z) f)⁻¹)⁻¹) 0 at h
    simpa only [inv_inv] using h

theorem originalRamifiedPlace_meromorphicOrderAt (N : ℕ) [NeZero N] (τ : ℍ)
    (f : modularFunctionFieldOver N ℂ) (hf0 : f ≠ 0) :
    meromorphicOrderAt (fun z => originalPlaceEval N ℂ (originalRamifiedPlace N τ z) f) 0 =
      ((originalAnalyticPlace N τ).ord f : WithTop ℤ) := by
  by_cases hf : f ∈ (originalAnalyticPlace N τ).toValuationSubring
  · exact originalRamifiedPlace_regular_order N τ f hf0 hf
  · have hi : f⁻¹ ∈ (originalAnalyticPlace N τ).toValuationSubring :=
      ((originalAnalyticPlace N τ).toValuationSubring.mem_or_inv_mem f).resolve_left hf
    have h := originalRamifiedPlace_regular_order N τ f⁻¹ (inv_ne_zero hf0) hi
    simp only [originalPlaceEval_inv, (originalAnalyticPlace N τ).ord_inv] at h
    change meromorphicOrderAt ((fun z => originalPlaceEval N ℂ (originalRamifiedPlace N τ z) f)⁻¹) 0 = _ at h
    rw [meromorphicOrderAt_inv] at h
    change -meromorphicOrderAt (fun z => originalPlaceEval N ℂ (originalRamifiedPlace N τ z) f) 0 =
      -((originalAnalyticPlace N τ).ord f : WithTop ℤ) at h
    exact neg_injective h

end
end Dubon2026.SourceFunctionField
