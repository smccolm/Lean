import TaoTrudgianYang2025.IvicSixthGramCardinality

/-! The proved global restricted moment closes the finite Gram estimate. -/

noncomputable section
open MeasureTheory
namespace TaoTrudgianYang2025

theorem exists_ivicSixth_physical_pattern_bound {η : ℝ} (hη : 0 < η)
    {q : ℕ} (hq : 0 < q) :
    ∃ C D T₀ : ℝ, 0 < C ∧ 0 < D ∧ 40000 ≤ T₀ ∧
      ∀ P : LargeValuePattern, T₀ ≤ P.T → ∀ H U : ℝ,
      0 ≤ H → H ≤ P.T → (4*P.T)^(11/72+η) ≤ U →
      4*C*P.N*Real.sqrt P.N*(2*H*U+(1+P.T)/(1+H)^(2*q)) ≤ P.V^2 →
      (P.ordinates.card:ℝ)*P.V^2 ≤ D*P.N^2 ∨
      (P.ordinates.card:ℝ)*P.V^12 ≤
        D*P.N^9*(2*H)^5*(2*H+1)*P.T^(1+η) := by
  obtain ⟨C,hC,hcard⟩ := exists_ivicSixth_gram_cardinality hq
  obtain ⟨A,B,hA,hB,hmoment⟩ := exists_ivicSixthExcess_symmetric_moment hη
  let D : ℝ := max (32*C) ((8*C)^6*A*(2:ℝ)^(1+η))
  have hD : 0 < D := lt_of_lt_of_le (by positivity : 0 < 32*C) (le_max_left _ _)
  refine ⟨C,D,B,hC,hD,hB,?_⟩
  intro P hT H U hH hHT hU hsmall
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp : 0 < P.T := P.T_pos
  rcases hcard P H U hH hsmall with hd | hm
  · left
    exact hd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  right
  have hthreshold : (2*(P.T+H))^(11/72+η) ≤ U := by
    apply le_trans _ hU
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hmoment := hmoment (P.T+H) U (by linarith) hthreshold
  have hp : (P.T+H)^(1+η) ≤ (2:ℝ)^(1+η)*P.T^(1+η) := by
    rw [← Real.mul_rpow (by norm_num) hTp.le]
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hint : (∫ v in -(P.T+H)..P.T+H,ivicSixthExcess U v^6) ≤
      A*(2:ℝ)^(1+η)*P.T^(1+η) := by
    exact hmoment.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hp hA.le)
  calc
    _ ≤ (8*C)^6*P.N^9*(2*H)^5*(2*H+1)*
        (A*(2:ℝ)^(1+η)*P.T^(1+η)) :=
      hm.trans (mul_le_mul_of_nonneg_left hint (by positivity))
    _ = ((8*C)^6*A*(2:ℝ)^(1+η))*
        (P.N^9*(2*H)^5*(2*H+1)*P.T^(1+η)) := by ring
    _ ≤ D*(P.N^9*(2*H)^5*(2*H+1)*P.T^(1+η)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _ = _ := by ring

end TaoTrudgianYang2025
