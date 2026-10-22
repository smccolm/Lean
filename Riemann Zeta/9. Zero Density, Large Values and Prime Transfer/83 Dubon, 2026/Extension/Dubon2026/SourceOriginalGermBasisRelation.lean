import Dubon2026.SourceOriginalChartReadFieldLaws

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
original-function comparison. A nontrivial relation between an original
divisor-space basis and a meromorphic multiple of another basis forces the
multiplier to be a quotient of original functions. Faithful chart germs and
basis independence prove that the denominator is nonzero.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem exists_original_function_of_basis_germ_relation
    {D₁ D₂ : Divisor ℂ (modularFunctionFieldOver N ℂ)} {a b : ℕ}
    (bf : Module.Basis (Fin a) ℂ (LSpace D₁))
    (be : Module.Basis (Fin b) ℂ (LSpace D₂))
    (q : Place ℂ (modularFunctionFieldOver N ℂ) → ℂ)
    (c : Fin a ⊕ Fin b → ℂ) (hc0 : c ≠ 0)
    (hc : ∀ v, (fun z =>
      (∑ i, c (Sum.inl i) * chartRead N v (bf i : modularFunctionFieldOver N ℂ) z) +
      ∑ j, c (Sum.inr j) * (q (placeFamily N v z) *
        chartRead N v (be j : modularFunctionFieldOver N ℂ) z)) =ᶠ[𝓝[≠] (0 : ℂ)] 0) :
    ∃ f : modularFunctionFieldOver N ℂ, ∀ v,
      (fun z => q (placeFamily N v z)) =ᶠ[𝓝[≠] (0 : ℂ)] chartRead N v f := by
  classical
  let wF : modularFunctionFieldOver N ℂ := ∑ i, c (Sum.inl i) • (bf i : modularFunctionFieldOver N ℂ)
  let uF : modularFunctionFieldOver N ℂ := ∑ j, c (Sum.inr j) • (be j : modularFunctionFieldOver N ℂ)
  have hrel : ∀ v, ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      chartRead N v wF z + q (placeFamily N v z) * chartRead N v uF z = 0 := by
    intro v
    filter_upwards [hc v,
      chartRead_sum_smul N Finset.univ v (fun i => c (Sum.inl i))
        (fun i => (bf i : modularFunctionFieldOver N ℂ)),
      chartRead_sum_smul N Finset.univ v (fun j => c (Sum.inr j))
        (fun j => (be j : modularFunctionFieldOver N ℂ))] with z hz hw hu
    rw [hw, hu, Finset.mul_sum]
    change (∑ i, c (Sum.inl i) * chartRead N v (bf i : modularFunctionFieldOver N ℂ) z) +
      (∑ j, q (placeFamily N v z) * (c (Sum.inr j) *
        chartRead N v (be j : modularFunctionFieldOver N ℂ) z)) = 0
    convert hz using 1
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have huF : uF ≠ 0 := by
    intro hu0
    have hinr : ∀ j, c (Sum.inr j) = 0 := by
      have hli := be.linearIndependent
      rw [Fintype.linearIndependent_iff] at hli
      apply hli (fun j => c (Sum.inr j))
      rw [← Submodule.coe_eq_zero, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact hu0
    have hwF : wF = 0 := by
      let v := originalAnalyticPlace N UpperHalfPlane.I
      apply eq_zero_of_chartRead_eventuallyEq_zero N v
      filter_upwards [hrel v] with z hz
      simpa only [hu0, chartRead_zero, Pi.zero_apply, mul_zero, add_zero] using hz
    have hinl : ∀ i, c (Sum.inl i) = 0 := by
      have hli := bf.linearIndependent
      rw [Fintype.linearIndependent_iff] at hli
      apply hli (fun i => c (Sum.inl i))
      rw [← Submodule.coe_eq_zero, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact hwF
    apply hc0
    funext i
    rcases i with i | j
    · exact hinl i
    · exact hinr j
  refine ⟨-wF * uF⁻¹, fun v => ?_⟩
  filter_upwards [hrel v, chartRead_mul N v (-wF) uF⁻¹,
    chartRead_neg N v wF, chartRead_inv N v huF,
    chartRead_eventually_ne_zero N v huF] with z hz hm hn hi hu
  rw [hm, Pi.mul_apply, hn, Pi.neg_apply, hi, Pi.inv_apply]
  field_simp
  linear_combination hz

end
end Dubon2026.SourceFunctionField.OriginalChart
