import TaoTrudgianYang2025.LiteratureDensity

/-! A positive endpoint improvement from an already proved analytic pair.
The stronger printed value 16/21 remains a separate open target. -/

noncomputable section
namespace TaoTrudgianYang2025


example (τ : ℝ) :
    IsLargeValueBound (39/40) τ (1/20+max 0 (τ-3277/890)) :=
  pintz_first_endpoint_pair_largeValueBound τ

example {τ : ℝ} (hlo : 21/8 ≤ τ) (hhi : τ ≤ 135765/36668) :
    largeValueExponent (39/40) τ ≤ ((2*τ/105:ℝ):EReal) :=
  largeValueExponent_le_pintz_first_endpoint_pair_range hlo hhi

example : zeroDensityExponent (39/40) ≤ ((3560/4399:ℝ):EReal) :=
  zeroDensityExponent_le_pintz_first_endpoint_pair

example : largeValueExponent (39/40) (135765/36668) ≤ ((1293/18334:ℝ):EReal) := by
  have hh := largeValueExponent_le_pintz_first_endpoint_pair_range
    (τ:=135765/36668) (by norm_num) le_rfl
  norm_num at hh
  exact hh

example : (16/21:ℝ) < 3560/4399 ∧ (3560/4399:ℝ) < 1424/1649 ∧
    (17/5:ℝ) < 135765/36668 ∧ (135765/36668:ℝ) < 63/16 := by norm_num

#print axioms pintz_first_endpoint_pair_largeValueBound
#print axioms largeValueExponent_le_pintz_first_endpoint_pair_range
#print axioms zeroDensityExponent_le_pintz_first_endpoint_pair


example {n : ℕ} (hn : 6 ≤ n) :
    IsLargeValueBound (1-1/(2*(n:ℝ)*((n:ℝ)-1)))
      ((n:ℝ)-2+2/(n:ℝ)) (1/((n:ℝ)*((n:ℝ)-1))) :=
  pintz_tail_endpoint_pair_largeValueBound hn

example {n : ℕ} (hn : 6 ≤ n) :
    zeroDensityExponent (1-1/(2*(n:ℝ)*((n:ℝ)-1))) ≤
      ((3/((n:ℝ)-2+2/(n:ℝ)+1/(2*(n:ℝ)*((n:ℝ)-1))):ℝ):EReal) :=
  zeroDensityExponent_le_pintz_tail_endpoint_pair hn

example : zeroDensityExponent (59/60) ≤ ((20/29:ℝ):EReal) := by
  have hh := zeroDensityExponent_le_pintz_tail_endpoint_pair (n:=6) (by omega)
  norm_num at hh
  exact hh

example : zeroDensityExponent (83/84) ≤ ((252/445:ℝ):EReal) := by
  have hh := zeroDensityExponent_le_pintz_tail_endpoint_pair (n:=7) (by omega)
  norm_num at hh
  exact hh

#print axioms pintz_tail_endpoint_pair_largeValueBound
#print axioms zeroDensityExponent_le_pintz_tail_endpoint_pair

end TaoTrudgianYang2025
