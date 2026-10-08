import Dubon2026.AdelicRaisingHilbertBasis

/-! # Exact original weight lines inside the genuine Hilbert closure -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Every smooth compact-weight vector in the original Hilbert closure lies on its exact original raising line. -/
theorem adelicRaisingClosedSpan_weight_line (hf : f ≠ 0) (hk : 0 < k) (n : ℕ)
    (v : adelicRealSmoothSubmodule f) (hv : v.val ∈ adelicRaisingClosedSpan f)
    (hH : ⁅compactSl2H, v⁆ = ((k : ℂ) + 2 * n) • v) :
    ∃ a : ℂ, v = a • adelicRaisingJet f n := by
  have hi (m : ℕ) (hmn : m ≠ n) : inner ℂ (adelicRaisingJet f m).val v.val = 0 := by
    apply symmetric_weight_inner_zero (adelicComplexSl2Action f compactSl2H)
      (adelicCompactSl2H_symmetric f) (adelicRaisingJet f m) v
      ((k : ℂ) + 2 * m) ((k : ℂ) + 2 * n) _ (adelicRaisingJet_weight f hf m) hH
    intro he
    apply hmn
    have he' : (m : ℂ) = n := by linear_combination he / 2
    exact_mod_cast he'
  obtain ⟨a, ha⟩ := @closureSpan_eq_smul_of_inner (AdelicCyclicHilbert f) ℕ
    inferInstance inferInstance (fun m => (adelicRaisingJet f m).val)
    (fun i j hij => adelicRaisingJet_inner_zero f hf i j hij) n
    (adelicRaisingJet_val_ne_zero f hf hk n) v.val hv hi
  exact ⟨a, Subtype.ext ha⟩

end
end Dubon2026
