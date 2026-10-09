import Dubon2026.GeneralLinearUnitDiagonal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Data.Finset.Max

/-! # A genuine maximal-valuation pivot for every original invertible two-by-two matrix -/

namespace Dubon2026

noncomputable section
open Matrix

/-- One actual nonzero matrix entry divides every original entry in the given valuation ring. -/
theorem valuationSubring_gl2_pivot {K : Type*} [Field K] (A : ValuationSubring K)
    (g : GeneralLinearGroup (Fin 2) K) :
    ∃ i j : Fin 2, g.val i j ≠ 0 ∧ ∀ r s : Fin 2, g.val r s / g.val i j ∈ A := by
  classical
  obtain ⟨ij, _, hij⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 2 × Fin 2))
    (fun rs => A.valuation (g.val rs.1 rs.2)) Finset.univ_nonempty
  have hmax (r s : Fin 2) : A.valuation (g.val r s) ≤ A.valuation (g.val ij.1 ij.2) :=
    hij (r, s) (Finset.mem_univ _)
  have hn : g.val ij.1 ij.2 ≠ 0 := by
    intro hz
    have he : g.val = 0 := by
      funext r s
      apply A.valuation.zero_iff.mp
      apply le_antisymm
      · simpa only [hz, map_zero] using hmax r s
      · exact zero_le
    exact (Units.ne_zero g) he
  refine ⟨ij.1, ij.2, hn, ?_⟩
  intro r s
  obtain ⟨a, ha⟩ := (A.valuation_le_iff (g.val r s) (g.val ij.1 ij.2)).mp (hmax r s)
  rw [← ha, mul_div_cancel_right₀ _ hn]
  exact a.property

end
end Dubon2026
