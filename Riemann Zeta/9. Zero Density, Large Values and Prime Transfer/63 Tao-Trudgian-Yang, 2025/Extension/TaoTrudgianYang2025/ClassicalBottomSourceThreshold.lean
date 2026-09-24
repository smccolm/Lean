import TaoTrudgianYang2025.ClassicalBottomSourceGeometry

/-!
# The bottom-source normalization loss

Both genuine dyadic counts and the detector threshold loss are absorbed.
The source line may differ from the target line; only 0 ≤ s ≤ 1 is used.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem classicalSource_successor_clog_le (A : ℕ) (hA : 1 ≤ A) :
    Nat.clog 2 (A+1) ≤ Nat.clog 2 A+1 := by
  apply Nat.clog_le_of_le_pow
  have hCover := Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) A
  rw [pow_succ]
  omega

theorem eventually_const_mul_classicalSource_two_clogs_le_rpow
    (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∀ᶠ T : ℝ in Filter.atTop,
      C*(Nat.clog 2 ⌊sharpZetaCutoff T⌋₊+1 : ℕ)*
        Nat.clog 2 (⌊sharpZetaCutoff T⌋₊+1) ≤ T^η := by
  filter_upwards [
    eventually_const_mul_classicalTypeI_clog_le_rpow (4*C) (η/2)
      (by positivity) (by positivity),
    eventually_const_mul_classicalTypeI_clog_le_rpow 1 (η/2)
      (by norm_num) (by positivity),
    Filter.eventually_ge_atTop (8 : ℝ)] with T hFirst hSecond hT
  let A := ⌊sharpZetaCutoff T⌋₊
  have hA : 1 < A := by
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4*T by linarith).trans (four_mul_lt_sharpZetaCutoff T).le
  have hL : (1 : ℝ) ≤ Nat.clog 2 A := by
    exact_mod_cast Nat.clog_pos Nat.one_lt_two hA
  have hSucc : (Nat.clog 2 (A+1) : ℝ) ≤ (Nat.clog 2 A : ℝ)+1 := by
    exact_mod_cast classicalSource_successor_clog_le A hA.le
  have hCount : ((Nat.clog 2 A+1 : ℕ) : ℝ) ≤ 2*(Nat.clog 2 A : ℝ) := by
    push_cast
    linarith
  have hCount' : (Nat.clog 2 (A+1) : ℝ) ≤ 2*(Nat.clog 2 A : ℝ) := by linarith
  have hTPos : 0 < T := by linarith
  calc
    C*(Nat.clog 2 A+1 : ℕ)*Nat.clog 2 (A+1) ≤
        C*(2*(Nat.clog 2 A : ℝ))*(2*(Nat.clog 2 A : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hCount hC) hCount'
        (Nat.cast_nonneg _) (by positivity)
    _ = ((4*C)*(Nat.clog 2 A : ℝ))*(1*(Nat.clog 2 A : ℝ)) := by ring
    _ ≤ T^(η/2)*T^(η/2) := mul_le_mul hFirst hSecond (by positivity) (by positivity)
    _ = T^η := by rw [← Real.rpow_add hTPos]; congr 1; ring

theorem classicalSource_annular_normalization_lower
    (N Q : ℕ) (s : ℝ) (hs : 0 ≤ s) (hsOne : s ≤ 1)
    (hQ : 0 < Q) (hNQ : N ≤ 2*Q) :
    (N : ℝ)^s ≤ 4*((Q : ℝ)/2)^s := by
  have hQPos : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc
    (N : ℝ)^s ≤ (2*(Q : ℝ))^s :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hNQ) hs
    _ = (4 : ℝ)^s*((Q : ℝ)/2)^s := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
      congr 1
      ring
    _ ≤ 4*((Q : ℝ)/2)^s := mul_le_mul_of_nonneg_right
      (by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hsOne)
      (Real.rpow_nonneg (by positivity) _)

theorem eventually_classicalBottomSource_normalized_threshold_lower
    (s b ε u : ℝ) (hs : 0 ≤ s) (hsOne : s ≤ 1)
    (hb : 0 < b) (hε : 0 < ε) (hu : u ≤ b*ε/2) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ N Q : ℕ,
      0 < Q → N ≤ 2*Q → T^b ≤ (N : ℝ) →
      (N : ℝ)^(s-ε) ≤
        ((((Q : ℝ)/2)^s)*
          (((3/4)*(T^(-u)/2))/(Nat.clog 2 ⌊sharpZetaCutoff T⌋₊+1 : ℕ)))/
            Nat.clog 2 (⌊sharpZetaCutoff T⌋₊+1) := by
  filter_upwards [
    eventually_const_mul_classicalSource_two_clogs_le_rpow (32/3) (b*ε/2)
      (by norm_num) (by positivity),
    Filter.eventually_ge_atTop (8 : ℝ)] with T hLog hT
  intro N Q hQ hNQ hScale
  let A := ⌊sharpZetaCutoff T⌋₊
  let L : ℝ := (Nat.clog 2 A+1 : ℕ)
  let k : ℝ := Nat.clog 2 (A+1)
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hNPos : (0 : ℝ) < N := (Real.rpow_pos_of_pos hTPos b).trans_le hScale
  have hA : 0 < A := by
    apply lt_of_lt_of_le (by omega : 0 < (1 : ℕ))
    apply Nat.le_floor
    simpa only [Nat.cast_one] using
      (show (1 : ℝ) ≤ 4*T by linarith).trans (four_mul_lt_sharpZetaCutoff T).le
  have hL : 0 < L := by dsimp [L]; positivity
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast Nat.clog_pos Nat.one_lt_two (by omega : 1 < A+1)
  have hDenPos : 0 < (32/3 : ℝ)*L*k*T^u := by positivity
  have hDen : (32/3 : ℝ)*L*k*T^u ≤ (N : ℝ)^ε := by
    calc
      (32/3 : ℝ)*L*k*T^u ≤ T^(b*ε/2)*T^u :=
        mul_le_mul_of_nonneg_right hLog (Real.rpow_nonneg hTPos.le _)
      _ = T^(b*ε/2+u) := (Real.rpow_add hTPos _ _).symm
      _ ≤ T^(b*ε) := Real.rpow_le_rpow_of_exponent_le hTOne (by linarith)
      _ = (T^b)^ε := Real.rpow_mul hTPos.le _ _
      _ ≤ (N : ℝ)^ε := Real.rpow_le_rpow (Real.rpow_nonneg hTPos.le _) hScale hε.le
  have hAnn := classicalSource_annular_normalization_lower N Q s hs hsOne hQ hNQ
  calc
    (N : ℝ)^(s-ε) = (N : ℝ)^s/(N : ℝ)^ε := Real.rpow_sub hNPos _ _
    _ ≤ (N : ℝ)^s/((32/3)*L*k*T^u) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hNPos.le _) hDenPos hDen
    _ ≤ (4*((Q : ℝ)/2)^s)/((32/3)*L*k*T^u) :=
      div_le_div_of_nonneg_right hAnn hDenPos.le
    _ = _ := by
      change _ = ((((Q : ℝ)/2)^s)*(((3/4)*(T^(-u)/2))/L))/k
      rw [Real.rpow_neg hTPos.le]
      have hTPow := Real.rpow_pos_of_pos hTPos u
      field_simp
      ring

end TaoTrudgianYang2025
