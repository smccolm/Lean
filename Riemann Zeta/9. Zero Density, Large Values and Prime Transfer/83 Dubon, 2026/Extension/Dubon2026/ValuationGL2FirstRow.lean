import Dubon2026.ValuationGL2Pivot

/-! # A genuine valuation pivot in the original first row -/

namespace Dubon2026

noncomputable section
open Matrix

/-- Every invertible two-by-two matrix has a nonzero first-row entry dividing the other first-row entry in the actual valuation ring. -/
theorem valuationSubring_gl2_firstRow_pivot {K : Type*} [Field K] (A : ValuationSubring K)
    (g : GeneralLinearGroup (Fin 2) K) :
    ∃ j : Fin 2, g.val 0 j ≠ 0 ∧ ∀ s : Fin 2, g.val 0 s / g.val 0 j ∈ A := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 2))
    (fun s => A.valuation (g.val 0 s)) Finset.univ_nonempty
  have hmax (s : Fin 2) : A.valuation (g.val 0 s) ≤ A.valuation (g.val 0 j) :=
    hj s (Finset.mem_univ s)
  have hn : g.val 0 j ≠ 0 := by
    intro hz
    have he (s : Fin 2) : g.val 0 s = 0 := by
      apply A.valuation.zero_iff.mp
      apply le_antisymm
      · simpa only [hz, map_zero] using hmax s
      · exact zero_le
    apply g.det_ne_zero
    rw [Matrix.det_fin_two, he 0, he 1, zero_mul, zero_mul, sub_self]
  refine ⟨j, hn, ?_⟩
  intro s
  obtain ⟨a, ha⟩ := (A.valuation_le_iff (g.val 0 s) (g.val 0 j)).mp (hmax s)
  rw [← ha, mul_div_cancel_right₀ _ hn]
  exact a.property

end
end Dubon2026
