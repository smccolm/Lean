import TaoTrudgianYang2025.IvicSixthPhysicalPatterns

/-! A physical small-power smoothing choice absorbs every source loss. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem ivicSixth_smoothing_tail_le {T η : ℝ} {q : ℕ}
    (hT : 1 ≤ T) (hq : 1 ≤ (2*q:ℕ)*η) :
    (1+T)/(1+T^η)^(2*q) ≤ 2 := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hH : 0 ≤ T^η := Real.rpow_nonneg hTp.le _
  have ht : T ≤ (T^η)^(2*q) := by
    rw [← Real.rpow_mul_natCast hTp.le]
    simpa only [Real.rpow_one,mul_comm] using
      Real.rpow_le_rpow_of_exponent_le hT hq
  have hd : T ≤ (1+T^η)^(2*q) :=
    ht.trans (pow_le_pow_left₀ hH (by linarith) _)
  apply (div_le_iff₀ (by positivity : 0 < (1+T^η)^(2*q))).mpr
  linarith

theorem ivicSixth_smoothing_window_le {T η : ℝ} (hT : 1 ≤ T) (hη : 0 ≤ η) :
    (2*T^η)^5*(2*T^η+1) ≤ 96*T^(6*η) := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hH : 1 ≤ T^η := Real.one_le_rpow hT hη
  calc
    _ ≤ (2*T^η)^5*(3*T^η) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 96*(T^η)^6 := by ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hTp.le]
      norm_num only [Nat.cast_ofNat]
      rw [mul_comm η]

theorem exists_ivicSixth_smoothed_pattern_bound {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ C D T₀ : ℝ, 0 < C ∧ 0 < D ∧ 40000 ≤ T₀ ∧
      ∀ P : LargeValuePattern, T₀ ≤ P.T →
      4*C*P.N*Real.sqrt P.N*P.T^(11/72+2*η) ≤ P.V^2 →
      (P.ordinates.card:ℝ)*P.V^2 ≤ D*P.N^2 ∨
      (P.ordinates.card:ℝ)*P.V^12 ≤ D*P.N^9*P.T^(1+7*η) := by
  obtain ⟨q,hq⟩ := exists_nat_gt (1/η)
  have hq0 : 0 < q := by
    have hh : (0:ℝ) < q := (div_pos (by norm_num) hη).trans hq
    exact_mod_cast hh
  have hqη : 1 ≤ (2*q:ℕ)*η := by
    have hh := (div_lt_iff₀ hη).mp hq
    push_cast
    nlinarith
  obtain ⟨A,B,T₀,hA,hB,hT₀,hphysical⟩ := exists_ivicSixth_physical_pattern_bound hη hq0
  let F : ℝ := 2*(4:ℝ)^(11/72+η)+2
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨A*F,96*B,T₀,by positivity,by positivity,hT₀,?_⟩
  intro P hT hsmall
  have hTp : 0 < P.T := P.T_pos
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hT1 : 1 ≤ P.T := by linarith
  have hH0 : 0 ≤ P.T^η := Real.rpow_nonneg hTp.le _
  have hHT : P.T^η ≤ P.T := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1 hη1
  have htail := ivicSixth_smoothing_tail_le hT1 hqη
  have hU : 2*P.T^η*(4*P.T)^(11/72+η) =
      (2*(4:ℝ)^(11/72+η))*P.T^(11/72+2*η) := by
    rw [Real.mul_rpow (by norm_num) hTp.le]
    calc
      _ = (2*(4:ℝ)^(11/72+η))*(P.T^η*P.T^(11/72+η)) := by ring
      _ = _ := by rw [← Real.rpow_add hTp]; congr 2; ring
  have hone : 1 ≤ P.T^(11/72+2*η) := Real.one_le_rpow hT1 (by linarith)
  have herror : 2*P.T^η*(4*P.T)^(11/72+η)+(1+P.T)/(1+P.T^η)^(2*q) ≤
      F*P.T^(11/72+2*η) := by
    rw [hU]
    dsimp [F]
    nlinarith
  have hentry : 4*A*P.N*Real.sqrt P.N*
      (2*P.T^η*(4*P.T)^(11/72+η)+(1+P.T)/(1+P.T^η)^(2*q)) ≤ P.V^2 := by
    apply le_trans (mul_le_mul_of_nonneg_left herror (by positivity))
    convert hsmall using 1
    ring
  rcases hphysical P hT (P.T^η) ((4*P.T)^(11/72+η)) hH0 hHT le_rfl hentry with
    hd | hm
  · left
    exact hd.trans (mul_le_mul_of_nonneg_right (by linarith : B ≤ 96*B) (sq_nonneg _))
  right
  have hwindow := ivicSixth_smoothing_window_le hT1 hη.le
  calc
    _ ≤ B*P.N^9*((2*P.T^η)^5*(2*P.T^η+1))*P.T^(1+η) := by
      simpa only [mul_assoc] using hm
    _ ≤ B*P.N^9*(96*P.T^(6*η))*P.T^(1+η) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwindow (by positivity))
        (by positivity)
    _ = (96*B)*P.N^9*(P.T^(6*η)*P.T^(1+η)) := by ring
    _ = _ := by rw [← Real.rpow_add hTp]; congr 2; ring

end TaoTrudgianYang2025
