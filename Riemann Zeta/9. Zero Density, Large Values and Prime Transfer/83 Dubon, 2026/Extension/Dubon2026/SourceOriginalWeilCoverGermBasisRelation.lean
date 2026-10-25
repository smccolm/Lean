import Dubon2026.SourceOriginalWeilCoverReadFieldLaws
import Dubon2026.SourceOriginalWeilCoverOnePole

/-! DUB-17/18 -> auxiliary Abel converse -> actual meromorphic field comparison.
A nontrivial relation between two actual cover divisor-space bases identifies
its analytic multiplier as a quotient in the same splitting field. Faithful
residue germs and basis independence prove the denominator is nonzero.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

theorem exists_cover_function_of_basis_germ_relation
    {D₁ D₂ : Divisor ℂ (EE)} {a b : ℕ}
    (bf : Module.Basis (Fin a) ℂ (LSpace D₁))
    (be : Module.Basis (Fin b) ℂ (LSpace D₂))
    (q : Place ℂ (EE) → ℂ)
    (c : Fin a ⊕ Fin b → ℂ) (hc0 : c ≠ 0)
    (hc : ∀ v, (fun z =>
      (∑ i, c (Sum.inl i) * chartRead N n r A hr hrA v (bf i : EE) z) +
      ∑ j, c (Sum.inr j) * (q (placeFamily N n r A hr hrA v z) *
        chartRead N n r A hr hrA v (be j : EE) z)) =ᶠ[𝓝[≠] (0 : ℂ)] 0) :
    ∃ f : EE, ∀ v,
      (fun z => q (placeFamily N n r A hr hrA v z)) =ᶠ[𝓝[≠] (0 : ℂ)] chartRead N n r A hr hrA v f := by
  classical
  let wF : EE := ∑ i, c (Sum.inl i) • (bf i : EE)
  let uF : EE := ∑ j, c (Sum.inr j) • (be j : EE)
  have hrel : ∀ v, ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      chartRead N n r A hr hrA v wF z + q (placeFamily N n r A hr hrA v z) * chartRead N n r A hr hrA v uF z = 0 := by
    intro v
    filter_upwards [hc v,
      chartRead_sum_smul N n r A hr hrA Finset.univ v (fun i => c (Sum.inl i))
        (fun i => (bf i : EE)),
      chartRead_sum_smul N n r A hr hrA Finset.univ v (fun j => c (Sum.inr j))
        (fun j => (be j : EE))] with z hz hw hu
    rw [hw, hu, Finset.mul_sum]
    change (∑ i, c (Sum.inl i) * chartRead N n r A hr hrA v (bf i : EE) z) +
      (∑ j, q (placeFamily N n r A hr hrA v z) * (c (Sum.inr j) *
        chartRead N n r A hr hrA v (be j : EE) z)) = 0
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
      let v := Classical.choice (nonempty_cover_place N n r)
      apply eq_zero_of_chartRead_eventuallyEq_zero N n r A hr hrA v
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
  filter_upwards [hrel v, chartRead_mul N n r A hr hrA v (-wF) uF⁻¹,
    chartRead_neg N n r A hr hrA v wF, chartRead_inv N n r A hr hrA v huF,
    chartRead_eventually_ne_zero N n r A hr hrA v huF] with z hz hm hn hi hu
  rw [hm, Pi.mul_apply, hn, Pi.neg_apply, hi, Pi.inv_apply]
  field_simp
  linear_combination hz

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
