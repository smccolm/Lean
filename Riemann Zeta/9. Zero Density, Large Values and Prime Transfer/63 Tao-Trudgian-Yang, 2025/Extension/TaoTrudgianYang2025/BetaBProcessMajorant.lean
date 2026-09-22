import TaoTrudgianYang2025.BetaDiscreteCurvature

/-! The finite B-process majorant at the source scales, with explicit
curvature constants and no asymptotic comparison used as a premise. -/

noncomputable section

namespace TaoTrudgianYang2025

def betaBProcessConstant (c C : ℝ) : ℝ :=
  (C/(2*Real.pi)+2)*((2*Real.pi+2)/Real.sqrt c+2)

theorem betaBProcessConstant_pos {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    0 < betaBProcessConstant c C := by
  unfold betaBProcessConstant
  positivity

theorem betaBProcess_majorant {m N T c C : ℝ}
    (hN : 0 < N) (hT : 0 < T) (hc : 0 < c) (hC : 0 ≤ C)
    (hm : m ≤ N) (hscale : T ≤ N^2) :
    (m*(C*T/N^2)/(2*Real.pi)+2)*
        (2*Real.pi/Real.sqrt (c*T/N^2)+2*(Real.sqrt (c*T/N^2)/(c*T/N^2)+1)) ≤
      betaBProcessConstant c C*(Real.sqrt T+N/Real.sqrt T) := by
  let y := Real.sqrt T
  let d := Real.sqrt c
  have hy : 0 < y := Real.sqrt_pos.mpr hT
  have hd : 0 < d := Real.sqrt_pos.mpr hc
  have hySq : y^2 = T := Real.sq_sqrt hT.le
  have hyN : y ≤ N := by
    rw [← Real.sqrt_sq hN.le]
    exact Real.sqrt_le_sqrt hscale
  have hratio : 1 ≤ N/y := (le_div_iff₀ hy).2 (by simpa using hyN)
  have hsqrt : Real.sqrt (c*T/N^2) = d*y/N := by
    rw [Real.sqrt_div (by positivity),Real.sqrt_mul hc.le,Real.sqrt_sq hN.le]
  have hfirst : m*(C*T/N^2)/(2*Real.pi)+2 ≤
      (C/(2*Real.pi)+2)*(T/N+1) := by
    calc
      m*(C*T/N^2)/(2*Real.pi)+2 ≤ N*(C*T/N^2)/(2*Real.pi)+2 := by
        gcongr
      _ = (C/(2*Real.pi))*(T/N)+2 := by field_simp
      _ ≤ (C/(2*Real.pi)+2)*(T/N+1) := by
        have : 0 ≤ C/(2*Real.pi) := by positivity
        have : 0 ≤ T/N := by positivity
        nlinarith
  have hsecond : 2*Real.pi/Real.sqrt (c*T/N^2)+
      2*(Real.sqrt (c*T/N^2)/(c*T/N^2)+1) ≤
      ((2*Real.pi+2)/d+2)*(N/y) := by
    rw [Real.sqrt_div_self',hsqrt]
    have heq : 2*Real.pi/(d*y/N)+2*(1/(d*y/N)+1) =
        ((2*Real.pi+2)/d)*(N/y)+2 := by field_simp; ring
    rw [heq]
    nlinarith
  have hmul := mul_le_mul hfirst hsecond
    (by positivity : 0 ≤ 2*Real.pi/Real.sqrt (c*T/N^2)+
      2*(Real.sqrt (c*T/N^2)/(c*T/N^2)+1))
    (by positivity : 0 ≤ (C/(2*Real.pi)+2)*(T/N+1))
  apply hmul.trans_eq
  change (C/(2*Real.pi)+2)*(T/N+1)*(((2*Real.pi+2)/d+2)*(N/y)) =
    (C/(2*Real.pi)+2)*((2*Real.pi+2)/d+2)*(y+N/y)
  have heq : (T/N+1)*(N/y) = y+N/y := by
    field_simp
    nlinarith [hySq]
  calc
    _ = (C/(2*Real.pi)+2)*((2*Real.pi+2)/d+2)*((T/N+1)*(N/y)) := by ring
    _ = _ := by rw [heq]

end TaoTrudgianYang2025
