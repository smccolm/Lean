import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> cover Abel converse -> extension from a simple-pole basis.
The finite coefficient identity used by the existing original-curve proof is
factored out so the actual-cover consumer elaborates within unchanged limits. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open scoped Classical

theorem sum_linear_combination_cycle_residue
    {R E C P : Type*} [Fintype R] [Fintype C]
    (L : Finset E) (S : Finset P) (U : C → Set P)
    (a : R → ℂ) (c : E → ℤ) (m : C → ℤ) (z : ℂ)
    (b : E → R → ℂ) (res : P → R → ℂ) :
    (∑ r, a r * (∑ l ∈ L, (c l : ℂ) * b l r +
      ∑ C, (m C : ℂ) * (z * ∑ v ∈ S.filter (fun v => v ∈ U C), res v r))) =
    (∑ l ∈ L, (c l : ℂ) * ∑ r, a r * b l r) +
      z * ∑ v ∈ S, ((∑ C, if v ∈ U C then m C else 0 : ℤ) : ℂ) *
        ∑ r, a r * res v r := by
  classical
  have h1 : ∑ r, a r * ∑ l ∈ L, (c l : ℂ) * b l r =
      ∑ l ∈ L, (c l : ℂ) * ∑ r, a r * b l r := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun r _ => by ring
  have h2 : ∑ r, a r * ∑ C, (m C : ℂ) * (z * ∑ v ∈ S.filter (fun v => v ∈ U C), res v r) =
      z * ∑ v ∈ S, ((∑ C, if v ∈ U C then m C else 0 : ℤ) : ℂ) * ∑ r, a r * res v r := by
    calc _ = z * ∑ C, (m C : ℂ) * ∑ r, a r * ∑ v ∈ S.filter (fun v => v ∈ U C), res v r := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun r _ =>
            Finset.sum_congr rfl fun v _ => by ring
      _ = z * ∑ C, (m C : ℂ) * ∑ v ∈ S.filter (fun v => v ∈ U C), ∑ r, a r * res v r := by
          congr 1
          apply Finset.sum_congr rfl
          intro C _
          congr 1
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
      _ = _ := by
          let t : P → ℂ := fun v => ∑ r, a r * res v r
          change z * (∑ C, (m C : ℂ) * ∑ v ∈ S.filter (fun v => v ∈ U C), t v) =
            z * ∑ v ∈ S, ((∑ C, if v ∈ U C then m C else 0 : ℤ) : ℂ) * t v
          congr 1
          simp_rw [Finset.sum_filter, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => ?_
          push_cast
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun C _ => ?_
          split_ifs <;> simp
  rw [Finset.sum_congr rfl fun r _ => mul_add (a r) _ _, Finset.sum_add_distrib, h1, h2]

end
end Dubon2026.SourceFunctionField.CellGeometry
