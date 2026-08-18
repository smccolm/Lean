import RiemannZeta.GuthMaynard.HughesYoungGlobalBounds

open Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

example (T : ℝ) :
    hughesYoungMollifierCoefficientMass T ≤
      ((detectorCutoff T : ℝ) ^ 4) := by
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  have hterm : ∀ h ∈ S,
      ‖shortMobiusSquareCoeff T h‖ ≤ ((detectorCutoff T : ℝ) ^ 2) := by
    intro h hh
    have hh0 : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1
    calc
      ‖shortMobiusSquareCoeff T h‖ ≤ (h.divisors.card : ℝ) :=
        norm_shortMobiusSquareCoeff_le_divisors T hh0
      _ ≤ (h : ℝ) := by exact_mod_cast Nat.card_divisors_le_self h
      _ ≤ ((detectorCutoff T : ℝ) ^ 2) := by
        exact_mod_cast (Finset.mem_Icc.mp hh).2
  unfold hughesYoungMollifierCoefficientMass
  change (∑ h ∈ S, ‖shortMobiusSquareCoeff T h‖) ≤ _
  calc
    (∑ h ∈ S, ‖shortMobiusSquareCoeff T h‖) ≤
        ∑ _h ∈ S, ((detectorCutoff T : ℝ) ^ 2) :=
      Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * ((detectorCutoff T : ℝ) ^ 2) := by simp
    _ ≤ ((detectorCutoff T : ℝ) ^ 2) *
        ((detectorCutoff T : ℝ) ^ 2) := by
      gcongr
      exact_mod_cast (show S.card ≤ (detectorCutoff T) ^ 2 by simp [S])
    _ = (detectorCutoff T : ℝ) ^ 4 := by ring

example {T : ℝ} (hT : 1 ≤ T) :
    hughesYoungMollifierCoefficientMass T ≤ 81 * T ^ (4 : ℝ) := by
  have hmass : hughesYoungMollifierCoefficientMass T ≤
      ((detectorCutoff T : ℝ) ^ 4) := by
    classical
    let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
    have hterm : ∀ h ∈ S,
        ‖shortMobiusSquareCoeff T h‖ ≤ ((detectorCutoff T : ℝ) ^ 2) := by
      intro h hh
      have hh0 : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1
      calc
        ‖shortMobiusSquareCoeff T h‖ ≤ (h.divisors.card : ℝ) :=
          norm_shortMobiusSquareCoeff_le_divisors T hh0
        _ ≤ (h : ℝ) := by exact_mod_cast Nat.card_divisors_le_self h
        _ ≤ ((detectorCutoff T : ℝ) ^ 2) := by
          exact_mod_cast (Finset.mem_Icc.mp hh).2
    unfold hughesYoungMollifierCoefficientMass
    change (∑ h ∈ S, ‖shortMobiusSquareCoeff T h‖) ≤ _
    calc
      (∑ h ∈ S, ‖shortMobiusSquareCoeff T h‖) ≤
          ∑ _h ∈ S, ((detectorCutoff T : ℝ) ^ 2) :=
        Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * ((detectorCutoff T : ℝ) ^ 2) := by simp
      _ ≤ ((detectorCutoff T : ℝ) ^ 2) *
          ((detectorCutoff T : ℝ) ^ 2) := by
        gcongr
        exact_mod_cast (show S.card ≤ (detectorCutoff T) ^ 2 by simp [S])
      _ = (detectorCutoff T : ℝ) ^ 4 := by ring
  have hcut := detectorCutoff_le_three_mul T hT
  calc
    hughesYoungMollifierCoefficientMass T ≤
        ((detectorCutoff T : ℝ) ^ 4) := hmass
    _ ≤ (3 * T) ^ 4 := by gcongr
    _ = 81 * T ^ (4 : ℝ) := by simp only [Real.rpow_ofNat]; ring

example {T : ℝ} (_hT : 1 ≤ T) :
    T ^ (5 : ℝ) ≤ (hughesYoungGlobalRadius T : ℝ) := by
  exact Nat.le_ceil (T ^ (5 : ℝ))

example {T : ℝ} (hT : 1 ≤ T) :
    (hughesYoungGlobalRadius T : ℝ) ^ (-199 : ℝ) ≤
      T ^ (-995 : ℝ) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hlower : T ^ (5 : ℝ) ≤ (hughesYoungGlobalRadius T : ℝ) :=
    Nat.le_ceil _
  have hneg := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hT0 (5 : ℝ)) hlower (by norm_num : (-199 : ℝ) ≤ 0)
  calc
    (hughesYoungGlobalRadius T : ℝ) ^ (-199 : ℝ) ≤
        (T ^ (5 : ℝ)) ^ (-199 : ℝ) := hneg
    _ = T ^ (-995 : ℝ) := by
      rw [← Real.rpow_mul hT0.le]
      norm_num

set_option maxRecDepth 10000 in
example :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, Real.exp 1 ≤ T →
      ‖hughesYoungActiveWholeSmoothedRemainder 100 T
          (hughesYoungGlobalRadius T) (hughesYoungGlobalDepth T)‖ ≤ C * T := by
  obtain ⟨L, hL, hrem⟩ :=
    exists_norm_hughesYoungActiveWholeSmoothedRemainder_le
      100 (by norm_num) (1 / 2 : ℝ) (by norm_num) (by norm_num)
  let C : ℝ :=
    (15 / 4) * 81 ^ 2 * (1 / Real.pi) *
      (256 * Real.exp (400 * (100 : ℝ) ^ 2) *
        207 ^ (408 : ℕ) *
        (hughesYoungReferenceDivisorPairMass (1 / 2) + 1) * L)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (by norm_num)) (by positivity))
      (mul_pos
        (mul_pos (mul_pos (by positivity) (by positivity))
          (by linarith [hughesYoungReferenceDivisorPairMass_nonneg (1 / 2)])) hL)
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hR := hughesYoungGlobalRadius_pos hT1
  have hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * hughesYoungGlobalRadius T : ℕ) : ℝ) ≤
            hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) := by
    intro h hh k hk
    exact hughesYoungGlobal_cover (by linarith [Real.exp_one_gt_d9]) hh hk
  have hraw := hrem hT hR hcover
  have hraw' :
      ‖hughesYoungActiveWholeSmoothedRemainder 100 T
          (hughesYoungGlobalRadius T) (hughesYoungGlobalDepth T)‖ ≤
        (15 * T / 4) * hughesYoungMollifierCoefficientMass T ^ 2 *
          (1 / Real.pi) *
          ((256 * Real.exp (400 * (100 : ℝ) ^ 2) *
            ((207 : ℝ) * T) ^ (408 : ℕ) *
            (hughesYoungGlobalRadius T : ℝ) ^ (-199 : ℝ) *
            hughesYoungReferenceDivisorPairMass (1 / 2)) * L) := by
    convert hraw using 1
    all_goals norm_num
  have hmass := hughesYoungMollifierCoefficientMass_le_height_fourth hT1
  have hmass0 := hughesYoungMollifierCoefficientMass_nonneg T
  have hpair0 := hughesYoungReferenceDivisorPairMass_nonneg (1 / 2)
  have hpair : hughesYoungReferenceDivisorPairMass (1 / 2) ≤
      hughesYoungReferenceDivisorPairMass (1 / 2) + 1 := by linarith
  have hrneg : (hughesYoungGlobalRadius T : ℝ) ^ (-199 : ℝ) ≤
      T ^ (-995 : ℝ) := by
    have hlower : T ^ (5 : ℝ) ≤ (hughesYoungGlobalRadius T : ℝ) :=
      Nat.le_ceil _
    have hneg := Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos hT0 (5 : ℝ)) hlower
        (by norm_num : (-199 : ℝ) ≤ 0)
    calc
      _ ≤ (T ^ (5 : ℝ)) ^ (-199 : ℝ) := hneg
      _ = T ^ (-995 : ℝ) := by
        rw [← Real.rpow_mul hT0.le]
        norm_num
  have hbound :
      (15 * T / 4) * hughesYoungMollifierCoefficientMass T ^ 2 *
          (1 / Real.pi) *
          ((256 * Real.exp (400 * (100 : ℝ) ^ 2) *
            ((207 : ℝ) * T) ^ (408 : ℕ) *
            (hughesYoungGlobalRadius T : ℝ) ^ (-199 : ℝ) *
            hughesYoungReferenceDivisorPairMass (1 / 2)) * L) ≤
        C * (T ^ (-578 : ℝ)) := by
    calc
      _ ≤
          (15 * T / 4) * (81 * T ^ (4 : ℝ)) ^ 2 *
            (1 / Real.pi) *
            ((256 * Real.exp (400 * (100 : ℝ) ^ 2) *
              ((207 : ℝ) * T) ^ (408 : ℕ) *
              T ^ (-995 : ℝ) *
              (hughesYoungReferenceDivisorPairMass (1 / 2) + 1)) * L) := by
        gcongr
      _ = C * T ^ (-578 : ℝ) := by
        have hfour : (T ^ (4 : ℝ)) ^ 2 = T ^ (8 : ℝ) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul hT0.le]
          norm_num
        have hpowers :
            T * T ^ (8 : ℝ) * T ^ (408 : ℕ) * T ^ (-995 : ℝ) =
              T ^ (-578 : ℝ) := by
          calc
            _ = T ^ (1 : ℝ) * T ^ (8 : ℝ) * T ^ (408 : ℝ) *
                T ^ (-995 : ℝ) := by
              rw [Real.rpow_one]
              exact congrArg
                (fun x : ℝ => T * T ^ (8 : ℝ) * x * T ^ (-995 : ℝ))
                (Real.rpow_natCast T 408).symm
            _ = T ^ ((1 : ℝ) + 8) * T ^ (408 : ℝ) * T ^ (-995 : ℝ) := by
              rw [← Real.rpow_add hT0]
            _ = T ^ ((1 : ℝ) + 8 + 408) * T ^ (-995 : ℝ) := by
              rw [← Real.rpow_add hT0]
            _ = T ^ ((1 : ℝ) + 8 + 408 - 995) := by
              rw [← Real.rpow_add hT0]
              norm_num
            _ = T ^ (-578 : ℝ) := by norm_num
        rw [mul_pow, hfour]
        calc
          _ = C *
              (T * T ^ (8 : ℝ) * T ^ (408 : ℕ) * T ^ (-995 : ℝ)) := by
            dsimp only [C]
            set_option exponentiation.threshold 512 in ring
          _ = C * T ^ (-578 : ℝ) := by rw [hpowers]
  have hlast : C * T ^ (-578 : ℝ) ≤ C * T := by
    have hp : T ^ (-578 : ℝ) ≤ T := by
      calc
        T ^ (-578 : ℝ) ≤ T ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
        _ = T := by simp
    exact mul_le_mul_of_nonneg_left hp hC.le
  exact hraw'.trans (hbound.trans hlast)

end RiemannZeta.GuthMaynard
