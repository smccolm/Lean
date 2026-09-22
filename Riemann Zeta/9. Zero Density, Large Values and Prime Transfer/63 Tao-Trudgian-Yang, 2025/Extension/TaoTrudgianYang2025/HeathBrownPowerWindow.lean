import TaoTrudgianYang2025.HeathBrownExponentAlgebra

/-!
# Physical power windows for Heath--Brown's three monomials

All exponents below are linked to the same actual T and N. The upper
scale window and explicit epsilon budgets produce the source beta bound.
-/

noncomputable section

namespace TaoTrudgianYang2025

def heathBrownPowerMajorant (k : ℕ) (η T N : ℝ) : ℝ :=
  N^η * (T^(heathBrownDerivativeExponent k) *
      N^(1-(k : ℝ)*heathBrownDerivativeExponent k) +
    N^(1-heathBrownDerivativeExponent k) +
    N*T^(-heathBrownInverseExponent k))

theorem heathBrown_monomial_window {T N α δ η p r : ℝ}
    (hT : 1 ≤ T) (hN : 0 < N) (hδ : 0 ≤ δ)
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (hwindow : N ≤ T^(α+δ)) :
    T^r*N^(p+η) ≤ T^(r+α*p+(α+1)*η+2*δ) := by
  have hTpos := zero_lt_one.trans_le hT
  have hpow := Real.rpow_le_rpow hN.le hwindow (add_nonneg hp hη)
  have hcost : (α+δ)*(p+η) ≤ α*p+(α+1)*η+2*δ := by
    have h₁ := mul_le_mul_of_nonneg_left hp₁ hδ
    have h₂ := mul_le_mul_of_nonneg_left hη₁ hδ
    nlinarith
  calc
    T^r*N^(p+η) ≤ T^r*(T^(α+δ))^(p+η) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hTpos.le _)
    _ = T^(r+(α+δ)*(p+η)) := by
      rw [← Real.rpow_mul hTpos.le,← Real.rpow_add hTpos]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by linarith)

theorem heathBrownPowerMajorant_window {k : ℕ} (hk : 3 ≤ k)
    {T N α δ η : ℝ} (hT : 1 ≤ T) (hN : 0 < N) (hδ : 0 ≤ δ)
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) (hwindow : N ≤ T^(α+δ)) :
    heathBrownPowerMajorant k η T N ≤
      3*T^(heathBrownBetaBound k α+(α+1)*η+2*δ) := by
  have hd := heathBrownDerivativeExponent_bounds hk
  have hkd : 0 ≤ (k : ℝ)*heathBrownDerivativeExponent k :=
    mul_nonneg (Nat.cast_nonneg k) hd.1.le
  have hp₁ : 0 ≤ 1-(k : ℝ)*heathBrownDerivativeExponent k := by linarith [hd.2.1]
  have hp₂ : 0 ≤ 1-heathBrownDerivativeExponent k := by linarith [hd.2.2]
  have hb₁ : heathBrownDerivativeExponent k+
      α*(1-(k : ℝ)*heathBrownDerivativeExponent k) ≤ heathBrownBetaBound k α := by
    rw [heathBrownBetaBound_eq_max hk]
    exact le_max_left _ _
  have hb₂ : α*(1-heathBrownDerivativeExponent k) ≤ heathBrownBetaBound k α := by
    rw [heathBrownBetaBound_eq_max hk]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hb₃ : α-heathBrownInverseExponent k ≤ heathBrownBetaBound k α := by
    rw [heathBrownBetaBound_eq_max hk]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have h₁ := heathBrown_monomial_window
    (r := heathBrownDerivativeExponent k) hT hN hδ hη hη₁ hp₁
    (by linarith) hwindow
  have h₂ := heathBrown_monomial_window (r := 0)
    hT hN hδ hη hη₁ hp₂ (by linarith [hd.1]) hwindow
  have h₃ := heathBrown_monomial_window (p := 1) (r := -heathBrownInverseExponent k)
    hT hN hδ hη hη₁ (by norm_num) le_rfl hwindow
  have hbound₁ := h₁.trans (Real.rpow_le_rpow_of_exponent_le hT
    (show heathBrownDerivativeExponent k+α*(1-(k : ℝ)*heathBrownDerivativeExponent k)+
      (α+1)*η+2*δ ≤ heathBrownBetaBound k α+(α+1)*η+2*δ by linarith))
  have hbound₂ := h₂.trans (Real.rpow_le_rpow_of_exponent_le hT
    (show 0+α*(1-heathBrownDerivativeExponent k)+(α+1)*η+2*δ ≤
      heathBrownBetaBound k α+(α+1)*η+2*δ by linarith))
  have hbound₃ := h₃.trans (Real.rpow_le_rpow_of_exponent_le hT
    (show -heathBrownInverseExponent k+α*1+(α+1)*η+2*δ ≤
      heathBrownBetaBound k α+(α+1)*η+2*δ by linarith))
  have he : heathBrownPowerMajorant k η T N =
      T^(heathBrownDerivativeExponent k)*N^((1-(k : ℝ)*heathBrownDerivativeExponent k)+η) +
      T^(0 : ℝ)*N^((1-heathBrownDerivativeExponent k)+η) +
      T^(-heathBrownInverseExponent k)*N^((1 : ℝ)+η) := by
    unfold heathBrownPowerMajorant
    rw [Real.rpow_add hN,Real.rpow_add hN,Real.rpow_add hN]
    simp only [Real.rpow_zero,Real.rpow_one]
    ring
  rw [he]
  linarith

theorem heathBrown_epsilon_budget {α ε : ℝ} (hα : 0 ≤ α) (hε : 0 < ε) :
    ∃ η δ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < δ ∧ δ ≤ 1 ∧
      (α+1)*η+2*δ ≤ ε := by
  let η := min 1 (ε/(4*(α+1)))
  let δ := min 1 (ε/8)
  have ha : 0 < α+1 := by linarith
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by norm_num))
  have hηcost : (α+1)*η ≤ ε/4 := by
    have he := mul_le_mul_of_nonneg_left (min_le_right 1 (ε/(4*(α+1)))) ha.le
    dsimp only [η]
    convert he using 1
    field_simp
  have hδcost : 2*δ ≤ ε/4 := by
    have hd := min_le_right 1 (ε/8)
    dsimp only [δ]
    linarith
  exact ⟨η,δ,hη,min_le_left _ _,hδ,min_le_left _ _,by linarith⟩

end TaoTrudgianYang2025
