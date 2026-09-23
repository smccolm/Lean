import TaoTrudgianYang2025.ExponentPair

/-! Exact C-process parameters and the quantitative low/high-height separation. -/

noncomputable section

namespace TaoTrudgianYang2025

def sargosCProcessK (k : ℝ) : ℝ := k/(12*(1+4*k))
def sargosCProcessL (k l : ℝ) : ℝ := (11*(1+4*k)+l)/(12*(1+4*k))
def sargosCProcessThreshold (k l : ℝ) : ℝ := (5+15*k+5*l)/(2+3*k)

theorem sargosCProcess_denominators_pos {k : ℝ} (hk : 0 ≤ k) :
    0 < 12*(1+4*k) ∧ 0 < 2+3*k := by constructor <;> linarith

theorem InExponentPairTriangle.sargosCProcess {k l : ℝ} (h : InExponentPairTriangle k l) :
    InExponentPairTriangle (sargosCProcessK k) (sargosCProcessL k l) := by
  have hd := (sargosCProcess_denominators_pos h.1).1
  have hk := h.1
  have hl := h.2.2.1
  have hlu := h.2.2.2.1
  unfold InExponentPairTriangle sargosCProcessK sargosCProcessL
  refine ⟨div_nonneg hk hd.le,(div_le_iff₀ hd).mpr (by linarith),
    (le_div_iff₀ hd).mpr (by linarith),(div_le_iff₀ hd).mpr (by linarith),?_⟩
  rw [← add_div]
  exact (div_le_iff₀ hd).mpr (by linarith)

theorem sargosCProcessThreshold_bounds {k l : ℝ} (h : InExponentPairTriangle k l) :
    15/4 ≤ sargosCProcessThreshold k l ∧ sargosCProcessThreshold k l ≤ 5 := by
  have hd := (sargosCProcess_denominators_pos h.1).2
  have hk := h.1
  have hl := h.2.2.1
  have hlu := h.2.2.2.1
  constructor
  · exact (le_div_iff₀ hd).mpr (by linarith)
  · exact (div_le_iff₀ hd).mpr (by linarith)

theorem sargosCProcessThreshold_secondary_identity {k l : ℝ} (hk : 0 ≤ k) :
    (1+k)*sargosCProcessThreshold k l-(1+k+3*l) =
      (1+4*k)*(3+3*k-l)/(2+3*k) := by
  have hd := (sargosCProcess_denominators_pos hk).2
  unfold sargosCProcessThreshold
  field_simp
  ring

theorem sargosCProcessThreshold_secondary_margin {k l : ℝ} (h : InExponentPairTriangle k l) :
    1 ≤ (1+k)*sargosCProcessThreshold k l-(1+k+3*l) := by
  rw [sargosCProcessThreshold_secondary_identity h.1]
  have hd := (sargosCProcess_denominators_pos h.1).2
  apply (le_div_iff₀ hd).mpr
  have hk := h.1
  have hlu := h.2.2.2.1
  have hp := mul_nonneg hk (show 0 ≤ 1-l by linarith)
  nlinarith [sq_nonneg k]

theorem sargosCProcessThreshold_cap_identity {k l : ℝ} (hk : 0 ≤ k) :
    3*k*sargosCProcessThreshold k l-(1+7*k-3*l) =
      (24*k^2-2*k+24*k*l+6*l-2)/(2+3*k) := by
  have hd := (sargosCProcess_denominators_pos hk).2
  unfold sargosCProcessThreshold
  field_simp
  ring

theorem sargosCProcessThreshold_cap_margin {k l : ℝ} (h : InExponentPairTriangle k l) :
    2/7 ≤ 3*k*sargosCProcessThreshold k l-(1+7*k-3*l) := by
  rw [sargosCProcessThreshold_cap_identity h.1]
  have hd := (sargosCProcess_denominators_pos h.1).2
  apply (le_div_iff₀ hd).mpr
  have hk := h.1
  have hku := h.2.1
  have hl := h.2.2.1
  have hp := mul_nonneg hk (show 0 ≤ l-1/2 by linarith)
  nlinarith [sq_nonneg k]

end TaoTrudgianYang2025
