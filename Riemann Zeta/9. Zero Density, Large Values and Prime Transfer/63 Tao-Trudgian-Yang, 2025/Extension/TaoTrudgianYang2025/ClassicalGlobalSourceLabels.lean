import TaoTrudgianYang2025.ClassicalReflectedSourceBounds

/-!
# All-index global smooth source selection

The actual long-tail lower bound is decomposed pointwise on its original
index type. The labels refer to the global Y,A cutoffs, not local Fin-2
smoothing of one sharp dyadic block.
-/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem exists_global_typeISourceSmoothBlock_indexed_labels
    {ι : Type*} [Fintype ι]
    (Y A k : ℕ) (sigma V : ℝ) (W : ι → ℝ)
    (hY : 1 ≤ Y) (hA : A ≤ 2^k*Y)
    (hLarge : ∀ x, V ≤
      ‖classicalZetaLongTail Y A ((sigma : ℂ)+Complex.I*(W x : ℂ))‖) :
    ∃ label : ι → Fin (k+1),
      (∀ x, V/(k+1 : ℕ) ≤
        ‖typeISourceSmoothBlock Y A (label x).val sigma (W x)‖) ∧
      (∀ x, (label x).val < 2 ∨ A < 2*(2^(label x).val*Y) ∨
        (((Y+1 : ℕ) : ℝ) ≤ (((2^(label x).val*Y : ℕ) : ℝ)/2) ∧
          2*(2^(label x).val*Y) ≤ A)) ∧
      Fintype.card ι = ∑ c : Fin (k+1), Fintype.card (EnergyColorFiber label c) := by
  classical
  have hEach := fun x => exists_typeISmoothBlock_large Y A k sigma (W x) V
    hY (Nat.succ_pos k) hA (hLarge x)
  choose r hr hValue using hEach
  let label : ι → Fin (k+1) := fun x => ⟨r x,Finset.mem_range.mp (hr x)⟩
  refine ⟨label,hValue,?_,cardinality_eq_sum_color_fibers label⟩
  intro x
  exact typeISourceSmoothScale_lower_terminal_or_interior hY

end TaoTrudgianYang2025

