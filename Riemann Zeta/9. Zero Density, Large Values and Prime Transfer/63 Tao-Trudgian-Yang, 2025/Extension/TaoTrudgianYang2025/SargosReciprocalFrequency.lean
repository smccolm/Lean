import TaoTrudgianYang2025.SargosFrequencyWindowCover
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Actual reciprocal quartic-frequency sum with only an arbitrarily small power loss. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_reciprocal_frequency_harmonic (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ H : ℕ, 1 ≤ H →
      ∑ q ∈ sargosLargeFrequencySextuples H, 12/|(sargosQuarticDifference q:ℝ)| ≤
        C*(H:ℝ)^ε*(1+Real.log (3*(H:ℝ))) := by
  obtain ⟨C,hC,hcount⟩ := sargosAbsoluteSextupleWindow_card_bound ε hε
  refine ⟨12*C,by linarith,?_⟩
  intro H hH
  have hHp : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hpow : (H:ℝ)^(3+ε) = (H:ℝ)^3*(H:ℝ)^ε := by
    rw [Real.rpow_add hHp]
    norm_num
  have hbin : ∀ j ∈ Finset.Icc 1 (3*H),
      (∑ q ∈ sargosAbsoluteSextupleWindow H ((j:ℝ)*(H:ℝ)^3) ((H:ℝ)^3),
        12/|(sargosQuarticDifference q:ℝ)|) ≤ (12*C*(H:ℝ)^ε)*(j:ℝ)⁻¹ := by
    intro j hj
    have hjp : (0:ℝ) < j := by exact_mod_cast (show 0 < j from (Finset.mem_Icc.mp hj).1)
    calc
      _ ≤ ((sargosAbsoluteSextupleWindow H ((j:ℝ)*(H:ℝ)^3) ((H:ℝ)^3)).card:ℝ)*
          (12/((j:ℝ)*(H:ℝ)^3)) :=
        sargosAbsoluteWindow_reciprocal_bound hH (Finset.mem_Icc.mp hj).1
      _ ≤ (C*(H:ℝ)^(3+ε))*(12/((j:ℝ)*(H:ℝ)^3)) :=
        mul_le_mul_of_nonneg_right (hcount H hH _) (by positivity)
      _ = _ := by
        rw [hpow]
        field_simp
  have hsum : (∑ j ∈ Finset.Icc 1 (3*H), (j:ℝ)⁻¹) ≤
      1+Real.log (3*(H:ℝ)) := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,
      Nat.cast_mul,Nat.cast_ofNat] using harmonic_le_one_add_log (3*H)
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 (3*H),
        ∑ q ∈ sargosAbsoluteSextupleWindow H ((j:ℝ)*(H:ℝ)^3) ((H:ℝ)^3),
          12/|(sargosQuarticDifference q:ℝ)| :=
      sargosLargeFrequency_sum_le_windows hH _ (fun q => by positivity)
    _ ≤ ∑ j ∈ Finset.Icc 1 (3*H), (12*C*(H:ℝ)^ε)*(j:ℝ)⁻¹ :=
      Finset.sum_le_sum hbin
    _ = (12*C*(H:ℝ)^ε)*(∑ j ∈ Finset.Icc 1 (3*H), (j:ℝ)⁻¹) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

theorem sargos_log_three_scale_le_rpow {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    1+Real.log (3*x) ≤ (1+Real.log 3+1/ε)*x^ε := by
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hlog := Real.log_le_rpow_div hxp.le hε
  have hp := Real.one_le_rpow hx hε.le
  have hc : 0 ≤ 1+Real.log 3 := by
    have hh : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    linarith
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hxp.ne']
  calc
    _ = (1+Real.log 3)+Real.log x := by ring
    _ ≤ (1+Real.log 3)*x^ε+x^ε/ε :=
      add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hc) hlog
    _ = _ := by ring

theorem sargos_reciprocal_frequency_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ H : ℕ, 1 ≤ H →
      ∑ q ∈ sargosLargeFrequencySextuples H, 12/|(sargosQuarticDifference q:ℝ)| ≤
        C*(H:ℝ)^ε := by
  have hhalf : 0 < ε/2 := by positivity
  obtain ⟨C,hC,hrec⟩ := sargos_reciprocal_frequency_harmonic (ε/2) hhalf
  let B := 1+Real.log 3+1/(ε/2)
  have hB : 1 ≤ B := by
    have hl : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have hi : 0 < 1/(ε/2) := by positivity
    dsimp [B]
    linarith
  refine ⟨C*B,one_le_mul_of_one_le_of_one_le hC hB,?_⟩
  intro H hH
  have hHr : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hHp : (0:ℝ) < H := zero_lt_one.trans_le hHr
  have hlog := sargos_log_three_scale_le_rpow hHr hhalf
  calc
    _ ≤ C*(H:ℝ)^(ε/2)*(1+Real.log (3*(H:ℝ))) := hrec H hH
    _ ≤ C*(H:ℝ)^(ε/2)*(B*(H:ℝ)^(ε/2)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = C*B*((H:ℝ)^(ε/2)*(H:ℝ)^(ε/2)) := by ring
    _ = C*B*(H:ℝ)^ε := by
      rw [← Real.rpow_add hHp,show ε/2+ε/2 = ε by ring]

end TaoTrudgianYang2025
