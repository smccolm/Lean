import Dubon2026.SourceOriginalMeromorphicDimension
import Dubon2026.SourceOriginalMeromorphicRRBounds
import Dubon2026.SourceOriginalGermBasisRelation

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
original-function comparison. Two actual original divisor-space bases exceed
the analytic pole-degree bound. Their nontrivial relation identifies every
meromorphic function with poles at one place as an original field element.
Only the existing Riemann-Roch inequality is used to size the spaces.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem exists_original_function_of_one_pole_bound
    (Q : Place ℂ (modularFunctionFieldOver N ℂ)) (n : ℕ)
    (q : Place ℂ (modularFunctionFieldOver N ℂ) → ℂ)
    (hq : ∀ v, MeromorphicAt (fun z => q (placeFamily N v z)) 0)
    (hord : ∀ v, ((-(Finsupp.single Q (n : ℤ)) v : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z => q (placeFamily N v z)) 0) :
    ∃ f : modularFunctionFieldOver N ℂ, ∀ v,
      (fun z => q (placeFamily N v z)) =ᶠ[𝓝[≠] (0 : ℂ)] chartRead N v f := by
  classical
  let m := 2 * originalGenus N ℂ
  let D₁ : Divisor ℂ (modularFunctionFieldOver N ℂ) := Finsupp.single Q ((n + m : ℕ) : ℤ)
  let D₂ : Divisor ℂ (modularFunctionFieldOver N ℂ) := Finsupp.single Q (m : ℤ)
  let DN : Place ℂ (modularFunctionFieldOver N ℂ) →₀ ℕ := Finsupp.single Q (n + m)
  letI := finite_original_lSpace N ℂ D₁
  letI := finite_original_lSpace N ℂ D₂
  let bf : Module.Basis (Fin (ell D₁)) ℂ (LSpace D₁) := Module.finBasis ℂ _
  let be : Module.Basis (Fin (ell D₂)) ℂ (LSpace D₂) := Module.finBasis ℂ _
  let ψ : Fin (ell D₁) ⊕ Fin (ell D₂) → Place ℂ (modularFunctionFieldOver N ℂ) → ℂ :=
    Sum.elim (fun i P => originalPlaceEval N ℂ P (bf i))
      (fun j P => q P * originalPlaceEval N ℂ P (be j))
  have hDN : ∀ v, (DN v : ℤ) = D₁ v := by
    intro v
    by_cases h : Q = v <;> simp [DN, D₁, h]
  have hψ : ∀ i v, MeromorphicAt (fun z => ψ i (placeFamily N v z)) 0 := by
    rintro (i | j) v
    · exact meromorphicAt_chartRead N v (bf i) (Metric.mem_ball_self (place_spec N v).1)
    · exact (hq v).mul (meromorphicAt_chartRead N v (be j) (Metric.mem_ball_self (place_spec N v).1))
  have ho : ∀ i v, ((-(DN v : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z => ψ i (placeFamily N v z)) 0 := by
    rintro (i | j) v
    · rw [hDN]
      exact chartRead_lSpace_order_bound N D₁ (bf i).2 v
    · have hm := meromorphicAt_chartRead N v (be j) (Metric.mem_ball_self (place_spec N v).1)
      have hb := add_le_add (hord v) (chartRead_lSpace_order_bound N D₂ (be j).2 v)
      rw [← WithTop.coe_add, ← meromorphicOrderAt_mul (hq v) hm] at hb
      have he : -(Finsupp.single Q (n : ℤ)) v + -D₂ v = -D₁ v := by
        by_cases h : Q = v <;> simp [D₁, D₂, h, Nat.cast_add]
        ring
      rw [he] at hb
      rw [hDN]
      exact hb
  have hcard : (DN.sum fun _ k => k) + 1 < Fintype.card (Fin (ell D₁) ⊕ Fin (ell D₂)) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    have hsum : (DN.sum fun _ k => k) = n + m :=
      Finsupp.sum_single_index (by rfl)
    rw [hsum]
    exact original_one_place_dimension_sum_gt N Q n
  obtain ⟨c, hc0, hc⟩ := exists_original_meromorphic_relation N DN ψ hψ ho hcard
  apply exists_original_function_of_basis_germ_relation N bf be q c hc0
  intro v
  simpa only [Fintype.sum_sum_type, ψ, Sum.elim_inl, Sum.elim_inr, chartRead] using hc v

end
end Dubon2026.SourceFunctionField.OriginalChart
