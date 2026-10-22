import Dubon2026.SourceOriginalMeromorphicPoleClearing
import Dubon2026.SourceOriginalOnePoleComparison

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
meromorphic exponentiation. Every analytic meromorphic function on the actual
original compact curve agrees in every punctured chart germ with one element
of the original function field. A proved original multiplier clears all but
one pole, the analytic dimension bound and original Riemann-Roch identify the
product, and division by the nonzero multiplier finishes the comparison.
No comparison, compactness, connectedness or Riemann-Roch hypothesis remains.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem exists_original_function_of_meromorphicAt
    (g : Place ℂ (modularFunctionFieldOver N ℂ) → ℂ)
    (hg : ∀ v, MeromorphicAt (fun z => g (placeFamily N v z)) 0) :
    ∃ f : modularFunctionFieldOver N ℂ, ∀ v,
      (fun z => g (placeFamily N v z)) =ᶠ[𝓝[≠] (0 : ℂ)] chartRead N v f := by
  let Q := originalAnalyticPlace N UpperHalfPlane.I
  obtain ⟨n, h, hh0, hh⟩ := exists_original_meromorphic_pole_clearing N Q g hg
  let q : Place ℂ (modularFunctionFieldOver N ℂ) → ℂ :=
    fun P => g P * originalPlaceEval N ℂ P h
  obtain ⟨f, hf⟩ := exists_original_function_of_one_pole_bound N Q n q
    (fun v => (hh v).1) (fun v => (hh v).2)
  refine ⟨f * h⁻¹, fun v => ?_⟩
  filter_upwards [hf v, chartRead_mul N v f h⁻¹, chartRead_inv N v hh0,
    chartRead_eventually_ne_zero N v hh0] with z hz hm hi hn
  change g (placeFamily N v z) * chartRead N v h z = chartRead N v f z at hz
  rw [hm, Pi.mul_apply, hi, Pi.inv_apply]
  field_simp
  exact hz

end
end Dubon2026.SourceFunctionField.OriginalChart
