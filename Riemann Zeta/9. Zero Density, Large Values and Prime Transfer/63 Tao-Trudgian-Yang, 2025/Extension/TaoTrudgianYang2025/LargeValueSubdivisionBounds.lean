import TaoTrudgianYang2025.LargeValueSubdivision
import TaoTrudgianYang2025.LargeValueBoundClosure
import TaoTrudgianYang2025.LargeValueNonnegative

/-! The full Huxley subdivision inequalities, with uniform source-pattern bounds. -/

noncomputable section

namespace TaoTrudgianYang2025

def LargeValuePattern.enlargeHeight (P : LargeValuePattern) (L : ℝ)
    (hL : P.T ≤ L) : LargeValuePattern :=
  { P with
    T := L
    intervalRight := P.intervalLeft+L
    T_pos := P.T_pos.trans_le hL
    interval_length := by ring
    ordinates_in_interval := by
      intro t ht
      have hp := P.ordinates_in_interval t ht
      exact ⟨hp.1,by linarith [P.interval_length]⟩ }

theorem IsLargeValueBound.of_height_le {σ τ τ' B : ℝ}
    (h : IsLargeValueBound σ τ' B) (hτ : τ ≤ τ') :
    IsLargeValueBound σ τ B := by
  intro ε hε
  obtain ⟨C,hC,δ,hδ,hb⟩ := h ε hε
  refine ⟨C,hC,δ/2,by positivity,?_⟩
  intro P hN _ hTu hVl hVu
  have hL : P.T ≤ P.N^(τ'+δ/2) :=
    hTu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
  let Q := P.enlargeHeight (P.N^(τ'+δ/2)) hL
  exact hb Q hN
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
    ((Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hVl)
    (hVu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)))

theorem IsLargeValueBound.subdivision {σ τ τ' B : ℝ}
    (h : IsLargeValueBound σ τ B) (hτ : τ ≤ τ') :
    IsLargeValueBound σ τ' (B+(τ'-τ)) := by
  intro ε hε
  obtain ⟨C,hC,δ,hδ,hb⟩ := h (ε/2) (by linarith)
  let d := min δ (ε/2)
  have hd : 0 < d := lt_min hδ (by linarith)
  have hdδ : d ≤ δ := min_le_left _ _
  have hdε : d ≤ ε/2 := min_le_right _ _
  refine ⟨2*C,by linarith,d,hd,?_⟩
  intro P hN _ hTu hVl hVu
  have hp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hL : 0 < P.N^τ := Real.rpow_pos_of_pos hp _
  have hlocal (j : ℕ) :
      (((P.localized (P.N^τ) hL j).ordinates.card):ℝ) ≤ C*P.N^(B+ε/2) := by
    apply hb (P.localized (P.N^τ) hL j) (by change C ≤ P.N; linarith)
    · exact Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)
    · exact Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)
    · exact (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hVl
    · exact hVu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
  have hratio : P.T/P.N^τ ≤ P.N^(τ'-τ+d) := by
    calc
      _ ≤ P.N^(τ'+d)/P.N^τ := div_le_div_of_nonneg_right hTu hL.le
      _ = _ := by rw [← Real.rpow_sub hp]; congr 1; ring
  have hf : ((Nat.floor (P.T/P.N^τ)+1:ℕ):ℝ) ≤ 2*P.N^(τ'-τ+d) := by
    have hfloor := Nat.floor_le (div_nonneg P.T_pos.le hL.le)
    have hone := Real.one_le_rpow P.one_lt_N.le (show 0 ≤ τ'-τ+d by linarith)
    push_cast
    linarith
  calc
    _ ≤ ((Nat.floor (P.T/P.N^τ)+1:ℕ):ℝ)*(C*P.N^(B+ε/2)) :=
      P.card_le_of_localized hL _ (fun j _ => hlocal j)
    _ ≤ (2*P.N^(τ'-τ+d))*(C*P.N^(B+ε/2)) :=
      mul_le_mul_of_nonneg_right hf (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg hp.le _))
    _ = (2*C)*P.N^((τ'-τ+d)+(B+ε/2)) := by
      rw [Real.rpow_add hp (τ'-τ+d) (B+ε/2)]
      ring
    _ ≤ (2*C)*P.N^((B+(τ'-τ))+ε) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)) (by linarith)

/-- Both source subdivision inequalities, including equal heights and height zero. -/
theorem largeValueExponent_subdivision {σ τ τ' : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) (hτ' : τ ≤ τ') :
    largeValueExponent σ τ ≤ largeValueExponent σ τ' ∧
      largeValueExponent σ τ' ≤ largeValueExponent σ τ+((τ'-τ:ℝ):EReal) := by
  have hf := largeValueExponent_coe_toReal hσ hσ₁ hτ
  have hf' := largeValueExponent_coe_toReal hσ hσ₁ (hτ.trans hτ')
  have hb : IsLargeValueBound σ τ (largeValueExponent σ τ).toReal :=
    isLargeValueBound_of_exponent_le (by rw [hf])
  have hb' : IsLargeValueBound σ τ' (largeValueExponent σ τ').toReal :=
    isLargeValueBound_of_exponent_le (by rw [hf'])
  constructor
  · simpa only [hf'] using largeValueExponent_le_of_bound (hb'.of_height_le hτ')
  · simpa only [EReal.coe_add,hf] using largeValueExponent_le_of_bound (hb.subdivision hτ')

end TaoTrudgianYang2025
