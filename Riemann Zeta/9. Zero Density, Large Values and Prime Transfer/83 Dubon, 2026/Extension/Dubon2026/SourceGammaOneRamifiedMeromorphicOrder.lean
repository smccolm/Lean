import Dubon2026.SourceGammaOneRamifiedRegularOrder
import Dubon2026.SourceCurveRationalChartValues

/-! DUB-17/18 -> actual Gamma1 period comparison -> complex place charts.
The original residue-value function is meromorphic on the descended
family for every original rational function, including poles. Inversion
reduces the pole case to the proved regular case. Every nonzero function
has exactly its original normalized order, with no ramification factor
and no supplied analytic realization or order-comparison hypothesis.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane CongruenceSubgroup

theorem meromorphicAt_ramifiedPlace_eval (N : ℕ) [NeZero N] (hT : ModularGroup.T ∈ Gamma1 N) (τ : ℍ)
    (f : functionFieldOver (Gamma1 N) ℂ) :
    MeromorphicAt (fun z => placeEval hT (ramifiedPlace N hT τ z) f) 0 := by
  by_cases hf : f ∈ (analyticPlace hT τ).toValuationSubring
  · exact (ramifiedPlace_regular_analytic N hT τ f hf).1.meromorphicAt
  · have hi : f⁻¹ ∈ (analyticPlace hT τ).toValuationSubring :=
      ((analyticPlace hT τ).toValuationSubring.mem_or_inv_mem f).resolve_left hf
    have h := (ramifiedPlace_regular_analytic N hT τ f⁻¹ hi).1.meromorphicAt.inv
    simp only [placeEval, SourceCurve.Place.rationalEval_inv] at h
    change MeromorphicAt (((fun z => placeEval hT (ramifiedPlace N hT τ z) f)⁻¹)⁻¹) 0 at h
    simpa only [inv_inv] using h

theorem ramifiedPlace_meromorphicOrderAt (N : ℕ) [NeZero N] (hT : ModularGroup.T ∈ Gamma1 N) (τ : ℍ)
    (f : functionFieldOver (Gamma1 N) ℂ) (hf0 : f ≠ 0) :
    meromorphicOrderAt (fun z => placeEval hT (ramifiedPlace N hT τ z) f) 0 =
      ((analyticPlace hT τ).ord f : WithTop ℤ) := by
  by_cases hf : f ∈ (analyticPlace hT τ).toValuationSubring
  · exact ramifiedPlace_regular_order N hT τ f hf0 hf
  · have hi : f⁻¹ ∈ (analyticPlace hT τ).toValuationSubring :=
      ((analyticPlace hT τ).toValuationSubring.mem_or_inv_mem f).resolve_left hf
    have h := ramifiedPlace_regular_order N hT τ f⁻¹ (inv_ne_zero hf0) hi
    simp only [placeEval, SourceCurve.Place.rationalEval_inv, (analyticPlace hT τ).ord_inv] at h
    change meromorphicOrderAt ((fun z => placeEval hT (ramifiedPlace N hT τ z) f)⁻¹) 0 = _ at h
    rw [meromorphicOrderAt_inv] at h
    change -meromorphicOrderAt (fun z => placeEval hT (ramifiedPlace N hT τ z) f) 0 =
      -((analyticPlace hT τ).ord f : WithTop ℤ) at h
    exact neg_injective h

end
end Dubon2026.SourceFunctionField.GammaOne
