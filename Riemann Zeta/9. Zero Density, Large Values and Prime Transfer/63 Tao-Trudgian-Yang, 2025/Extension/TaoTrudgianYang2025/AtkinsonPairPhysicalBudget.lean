import TaoTrudgianYang2025.AtkinsonPairPhysicalScale

/-! Closed physical budget for the actual general-pair dyadic consumer. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem atkinsonPairPowerTerm_physical_le {C H G L k l : ℝ} {N : ℕ} (R : ℕ)
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hG : 1 ≤ G)
    (hL : 0 ≤ L) (hLH : L ≤ H) (hlog : 1 ≤ Real.log (2*H))
    (hpair : InExponentPairTriangle k l)
    (hcut : (N : ℝ) ≤ 74*H*(Real.log (2*H))^2/G^2) :
    G^2*H^(-(1/2:ℝ))*atkinsonPairPowerTerm C k l H G L N R ≤
      10000*C*(Real.log (2*H))^3*
        ((R : ℝ)*H/G+(R : ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l)) := by
  have hH0 : 0 < H := by linarith
  have hG0 : 0 < G := by linarith
  have hlog0 : 0 < Real.log (2*H) := by linarith
  have hp : 0 ≤ l+1/2-k/2 := by
    rcases hpair with ⟨_,hk,hl,_,_⟩
    linarith
  let P := G^2*H^(-(1/2:ℝ))
  let B := 74*H*(Real.log (2*H))^2/G^2
  let K := (harmonic (Nat.ceil (L/G)) : ℝ)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hK : 0 ≤ K := by
    simpa only [harmonic_zero,Rat.cast_zero] using
      atkinson_harmonic_mono (Nat.zero_le (Nat.ceil (L/G)))
  have hk : K ≤ 2*Real.log (2*H) :=
    atkinson_pair_harmonic_le_height_log hH hG hLH hlog
  have hd : P*(N : ℝ)^(3/2:ℝ) ≤ 5476*(H/G)*(Real.log (2*H))^3 := by
    calc
      _ ≤ P*B^(3/2:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg N) hcut (by norm_num)) hP
      _ ≤ _ := atkinsonPhysical_diagonal_scale hH0 hG0 hlog0
  have hn : (Real.sqrt H/G)*(P*(N : ℝ)) ≤
      74*(H/G)*(Real.log (2*H))^2 := by
    calc
      _ ≤ (Real.sqrt H/G)*(P*B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcut hP) (by positivity)
      _ = _ := by simpa only [Real.rpow_one] using
        atkinsonPhysical_near_scale hH0 hG0 hlog0
  have hf : (L^k*H^(-k/2))*(P*(N : ℝ)^(l+1/2-k/2)) ≤
      5476*(Real.log (2*H))^3*(L^k*H^(l-k)*G^(1+k-2*l)) := by
    calc
      _ ≤ (L^k*H^(-k/2))*(P*B^(l+1/2-k/2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg N) hcut hp) hP) (by positivity)
      _ ≤ _ := atkinsonPhysical_pair_scale_le hH0 hG0 hlog hL hpair
  have h1 := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg R : (0 : ℝ) ≤ _)
  have h2 := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ C*(R : ℝ)^2)
  have h3 := mul_le_mul
    (mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 2*C*(R : ℝ)))
    hk hK (by positivity)
  have he : P*atkinsonPairPowerTerm C k l H G L N R =
      (R : ℝ)*(P*(N : ℝ)^(3/2:ℝ))+
      C*(R : ℝ)^2*((L^k*H^(-k/2))*(P*(N : ℝ)^(l+1/2-k/2)))+
      (2*C*(R : ℝ)*((Real.sqrt H/G)*(P*(N : ℝ))))*K := by
    unfold atkinsonPairPowerTerm K
    ring
  change P*atkinsonPairPowerTerm C k l H G L N R ≤ _
  rw [he]
  apply (add_le_add (add_le_add h1 h2) h3).trans
  let X := (R : ℝ)*(H/G)*(Real.log (2*H))^3
  let Y := (R : ℝ)^2*(L^k*H^(l-k)*G^(1+k-2*l))*(Real.log (2*H))^3
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  calc
    _ = (5476+296*C)*X+5476*C*Y := by dsimp [X,Y]; ring
    _ ≤ (10000*C)*X+(10000*C)*Y := add_le_add
      (mul_le_mul_of_nonneg_right (by linarith) hX)
      (mul_le_mul_of_nonneg_right (by linarith) hY)
    _ = _ := by dsimp [X,Y]; ring

theorem atkinsonPairPowerBudget_physical_log_le {C H G L k l : ℝ} {N : ℕ} (R : ℕ)
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hG : 1 ≤ G)
    (hL : 0 ≤ L) (hLH : L ≤ H) (hlog : 1 ≤ Real.log (2*H))
    (hpair : InExponentPairTriangle k l) (hN : (N : ℝ) ≤ H)
    (hcut : (N : ℝ) ≤ 74*H*(Real.log (2*H))^2/G^2) :
    G^2*H^(-(1/2:ℝ))*atkinsonPairPowerBudget C k l H G L N R ≤
      (10000*C*(1/Real.log 2+1)^2)*(Real.log (2*H))^5*
        ((R : ℝ)*H/G+(R : ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l)) := by
  have ht := atkinsonPairPowerTerm_physical_le R hC hH hG hL hLH hlog hpair hcut
  have hj := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.clog 2 N) : (0 : ℝ) ≤ _)
    (atkinson_clog_le_height_log hH hlog hN) 2
  unfold atkinsonPairPowerBudget
  calc
    _ = (Nat.clog 2 N : ℝ)^2*
        (G^2*H^(-(1/2:ℝ))*atkinsonPairPowerTerm C k l H G L N R) := by ring
    _ ≤ (Nat.clog 2 N : ℝ)^2*
        (10000*C*(Real.log (2*H))^3*
          ((R : ℝ)*H/G+(R : ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l))) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg _)
    _ ≤ ((1/Real.log 2+1)*Real.log (2*H))^2*
        (10000*C*(Real.log (2*H))^3*
          ((R : ℝ)*H/G+(R : ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l))) :=
      mul_le_mul_of_nonneg_right hj (by positivity)
    _ = _ := by ring

end TaoTrudgianYang2025
