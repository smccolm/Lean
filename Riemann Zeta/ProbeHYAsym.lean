import RiemannZeta.GuthMaynard.HughesYoungNative

open Asymptotics Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

theorem probe_depth_bound {δ T : ℝ} (hδ : 0 < δ) (hT : Real.exp 1 ≤ T) :
    ((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ≤
      (100 / δ + 3) * T ^ δ := by
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hceil := Nat.ceil_lt_add_one
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) hlog0)
  have hlog := Real.log_le_rpow_div (zero_le_one.trans hT1) hδ
  have hpow1 : 1 ≤ T ^ δ := Real.one_le_rpow hT1 hδ.le
  unfold hughesYoungGlobalDepth
  push_cast
  exact (calc
    (⌈100 * Real.log T⌉₊ : ℝ) + 2 <
        100 * Real.log T + 3 := by linarith
    _ ≤ 100 * (T ^ δ / δ) + 3 := by gcongr
    _ ≤ (100 / δ + 3) * T ^ δ := by
      rw [show (100 / δ + 3) * T ^ δ =
          100 * (T ^ δ / δ) + 3 * T ^ δ by field_simp]
      linarith).le

theorem probe_active_cutoff_bound {T : ℝ} (hT : Real.exp 1 ≤ T) :
    (hughesYoungActiveArithmeticCutoff T (hughesYoungGlobalRadius T) : ℝ) ≤
      649 * T ^ (9 : ℝ) := by
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hcut := detectorCutoff_le_three_mul T hT1
  have hell : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ 9 * T ^ (2 : ℝ) := by
    rw [Nat.cast_pow, Real.rpow_two]
    nlinarith
  have hellReal : (detectorCutoff T : ℝ) ^ 2 ≤ 9 * T ^ (2 : ℝ) := by
    simpa only [Nat.cast_pow] using hell
  have hR := hughesYoungGlobalRadius_le hT1
  have hprod : ((((detectorCutoff T) ^ 2 * (detectorCutoff T) ^ 2 *
      hughesYoungGlobalRadius T : ℕ) : ℝ)) ≤ 162 * T ^ (9 : ℝ) := by
    push_cast
    calc
      _ ≤ (9 * T ^ (2 : ℝ)) * (9 * T ^ (2 : ℝ)) *
          (2 * T ^ (5 : ℝ)) := by gcongr
      _ = 162 * T ^ (9 : ℝ) := by
        simp only [Real.rpow_ofNat]
        ring
  have hp : 1 ≤ T ^ (9 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  calc
    (hughesYoungActiveArithmeticCutoff T (hughesYoungGlobalRadius T) : ℝ) =
        4 * ((((detectorCutoff T) ^ 2 * (detectorCutoff T) ^ 2 *
          hughesYoungGlobalRadius T : ℕ) : ℝ)) + 1 := by
          unfold hughesYoungActiveArithmeticCutoff
          push_cast
          ring
    _ ≤ 4 * (162 * T ^ (9 : ℝ)) + 1 := by gcongr
    _ ≤ 649 * T ^ (9 : ℝ) := by nlinarith

theorem probe_combined_cutoff_bound {T : ℝ} (hT : Real.exp 1 ≤ T) :
    ((((detectorCutoff T) ^ 2 *
      hughesYoungActiveArithmeticCutoff T (hughesYoungGlobalRadius T) : ℕ) : ℝ)) ≤
      5841 * T ^ (11 : ℝ) := by
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hcut := detectorCutoff_le_three_mul T hT1
  have hell : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤ 9 * T ^ (2 : ℝ) := by
    rw [Nat.cast_pow, Real.rpow_two]
    nlinarith
  have hellReal : (detectorCutoff T : ℝ) ^ 2 ≤ 9 * T ^ (2 : ℝ) := by
    simpa only [Nat.cast_pow] using hell
  have hB := probe_active_cutoff_bound hT
  calc
    _ = (detectorCutoff T : ℝ) ^ 2 *
        (hughesYoungActiveArithmeticCutoff T (hughesYoungGlobalRadius T) : ℝ) := by
          push_cast
          ring
    _ ≤ (9 * T ^ (2 : ℝ)) * (649 * T ^ (9 : ℝ)) := by gcongr
    _ = 5841 * T ^ (11 : ℝ) := by
      simp only [Real.rpow_ofNat]
      ring

theorem probe_active_diagonal_le_power
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C W ca cd : ℝ,
      0 < C ∧ 0 < W ∧ 0 < ca ∧ 0 < cd ∧
      ∀ {T H : ℝ} {R K : ℕ}, Real.exp 1 ≤ T → 0 ≤ H →
        ‖hughesYoungActiveFiniteDiagonal T H R K‖ ≤
          ((K + 2 : ℕ) : ℝ) ^ 2 *
          ((15 * T / 4) * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * W *
              Real.sqrt (Real.pi / 80))) *
          ca ^ 2 * cd ^ 4 *
          ((((detectorCutoff T) ^ 2 *
            hughesYoungActiveArithmeticCutoff T R : ℕ) : ℝ)) ^ (6 * δ) *
          (((harmonic ((detectorCutoff T) ^ 2 *
            hughesYoungActiveArithmeticCutoff T R) : ℚ) : ℝ)) := by
  obtain ⟨C, W, hC, hW, hdiag⟩ :=
    exists_norm_hughesYoungActiveFiniteDiagonal_le
  obtain ⟨ca, hca, hcoeff⟩ := shortMobiusSquareCoeff_bound δ hδ
  obtain ⟨cd, hcd, hdiv⟩ := divisorCountBound_native δ hδ
  refine ⟨C, W, ca, cd, hC, hW, hca, hcd, ?_⟩
  intro T H R K hT hH
  let ell : ℕ := (detectorCutoff T) ^ 2
  let B : ℕ := hughesYoungActiveArithmeticCutoff T R
  let cutoff : ℕ := ell * B
  let F : ℝ := (15 * T / 4) * (1 / Real.pi) *
    (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hF0 : 0 ≤ F := by
    have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
    have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
    dsimp only [F]
    positivity
  have hdiag' := hdiag (T := T) (H := H) (R := R) (K := K) hT hH
  have hmajor := hughesYoungFiniteDiagonalArithmeticMajorant_le T ell B
  have hsmooth := smoothTwistedDiagonalMajorant_le
    (ell := ell) (cutoff := cutoff) hT0.le
    (shortMobiusSquareCoeff T) hδ.le hca.le hcd.le
    (fun h hh => hcoeff T h (Finset.mem_Icc.mp hh).1) hdiv
  have hsum :
      (∑ q ∈ Finset.Icc 1 cutoff,
        smoothTwistedDiagonalFiber ell q (shortMobiusSquareCoeff T) ^ 2 *
          (q : ℝ)⁻¹) ≤
        ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * δ) *
          (((harmonic cutoff : ℚ) : ℝ)) := by
    unfold smoothTwistedDiagonalMajorant at hsmooth
    have hfactor : 0 < 5 * T / 2 := by positivity
    nlinarith
  change _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * F *
    ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * δ) *
      (((harmonic cutoff : ℚ) : ℝ))
  calc
    _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * F *
        hughesYoungFiniteDiagonalArithmeticMajorant T ell B := by
      simpa only [F, ell, B] using hdiag'
    _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * F *
        (∑ q ∈ Finset.Icc 1 cutoff,
          smoothTwistedDiagonalFiber ell q (shortMobiusSquareCoeff T) ^ 2 *
            (q : ℝ)⁻¹) := by
      gcongr
    _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * F *
        (ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * δ) *
          (((harmonic cutoff : ℚ) : ℝ))) := by
      gcongr
    _ = _ := by ring

theorem probe_active_diagonal_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungActiveFiniteDiagonal T (T / 8)
        (hughesYoungGlobalRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  let δ : ℝ := ε / 100
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨C, W, ca, cd, hC, hW, hca, hcd, hdiag⟩ :=
    probe_active_diagonal_le_power δ hδ
  let A : ℝ :=
    (100 / δ + 3) ^ 2 *
      ((15 / 4) * (1 / Real.pi) *
        (δ⁻¹ * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))) *
      ca ^ 2 * cd ^ 4 * (1 + δ⁻¹) * (5841 : ℝ) ^ (7 * δ)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  apply IsBigO.of_bound A
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  let Q : ℕ := (detectorCutoff T) ^ 2 *
    hughesYoungActiveArithmeticCutoff T (hughesYoungGlobalRadius T)
  have hQone : 1 ≤ Q := by
    dsimp only [Q]
    have hc : 0 < detectorCutoff T := by simp [detectorCutoff]
    have hB : 0 < hughesYoungActiveArithmeticCutoff T
        (hughesYoungGlobalRadius T) := by
      unfold hughesYoungActiveArithmeticCutoff
      omega
    exact Nat.mul_pos (pow_pos hc 2) hB
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hQbound : (Q : ℝ) ≤ 5841 * T ^ (11 : ℝ) := by
    simpa only [Q] using probe_combined_cutoff_bound hT
  have hHarm := harmonic_le_epsilon_rpow hδ Q
  have hmax : max 1 ((Q : ℝ) ^ δ) = (Q : ℝ) ^ δ :=
    max_eq_right (Real.one_le_rpow (by exact_mod_cast hQone) hδ.le)
  rw [hmax] at hHarm
  have hQpower : (Q : ℝ) ^ (7 * δ) ≤
      (5841 : ℝ) ^ (7 * δ) * T ^ (77 * δ) := by
    calc
      (Q : ℝ) ^ (7 * δ) ≤
          (5841 * T ^ (11 : ℝ)) ^ (7 * δ) := by
            exact Real.rpow_le_rpow hQ0 hQbound (by positivity)
      _ = (5841 : ℝ) ^ (7 * δ) *
          (T ^ (11 : ℝ)) ^ (7 * δ) := by
            rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT0.le _)]
      _ = (5841 : ℝ) ^ (7 * δ) * T ^ (77 * δ) := by
            rw [← Real.rpow_mul hT0.le]
            congr 1
            ring
  have hQcombine : (Q : ℝ) ^ (6 * δ) *
      (((harmonic Q : ℚ) : ℝ)) ≤
        (1 + δ⁻¹) * (5841 : ℝ) ^ (7 * δ) * T ^ (77 * δ) := by
    calc
      _ ≤ (Q : ℝ) ^ (6 * δ) *
          ((1 + δ⁻¹) * (Q : ℝ) ^ δ) := by
            gcongr
      _ = (1 + δ⁻¹) * (Q : ℝ) ^ (7 * δ) := by
            have hQRpos : (0 : ℝ) < Q := by exact_mod_cast hQone
            rw [show 7 * δ = 6 * δ + δ by ring,
              Real.rpow_add hQRpos]
            ring
      _ ≤ (1 + δ⁻¹) *
          ((5841 : ℝ) ^ (7 * δ) * T ^ (77 * δ)) :=
            mul_le_mul_of_nonneg_left hQpower (by positivity)
      _ = _ := by ring
  have hdepth := probe_depth_bound hδ hT
  have hdepthSq : (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) ≤
      (100 / δ + 3) ^ 2 * T ^ (2 * δ) := by
    calc
      _ ≤ ((100 / δ + 3) * T ^ δ) ^ 2 := by gcongr
      _ = (100 / δ + 3) ^ 2 * T ^ (2 * δ) := by
        rw [mul_pow]
        rw [show (T ^ δ) ^ 2 = T ^ (2 * δ) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
          ring_nf]
  have hlog : Real.log T ≤ δ⁻¹ * T ^ δ := by
    have := Real.log_le_rpow_div hT0.le hδ
    simpa [div_eq_mul_inv, mul_comm] using this
  let G : ℝ := (15 / 4) * (1 / Real.pi) *
    (δ⁻¹ * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    positivity
  have hfactor0 : 0 ≤ (15 * T / 4) * (1 / Real.pi) *
      (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80)) := by
    have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
    positivity
  have hfactor : (15 * T / 4) * (1 / Real.pi) *
      (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80)) ≤
        G * T ^ (1 + δ) := by
    calc
      _ ≤ (15 * T / 4) * (1 / Real.pi) *
          ((δ⁻¹ * T ^ δ) * Real.exp (4 * C) * W *
            Real.sqrt (Real.pi / 80)) := by gcongr
      _ = G * T ^ (1 + δ) := by
        dsimp only [G]
        have hp : T * T ^ δ = T ^ (1 + δ) := by
          calc
            T * T ^ δ = T ^ (1 : ℝ) * T ^ δ := by rw [Real.rpow_one]
            _ = T ^ ((1 : ℝ) + δ) := (Real.rpow_add hT0 1 δ).symm
        rw [← hp]
        ring
  have hharm0 : 0 ≤ (((harmonic Q : ℚ) : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hpowcombine : T ^ (2 * δ) * T ^ (1 + δ) * T ^ (77 * δ) =
      T ^ (1 + 80 * δ) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
    congr 1
    ring
  have hraw := hdiag (T := T) (H := T / 8)
    (R := hughesYoungGlobalRadius T) (K := hughesYoungGlobalDepth T)
    hT (by positivity)
  have hbound :
      ‖hughesYoungActiveFiniteDiagonal T (T / 8)
        (hughesYoungGlobalRadius T) (hughesYoungGlobalDepth T)‖ ≤
        A * T ^ (1 + 80 * δ) := by
    calc
      _ ≤ (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) *
          ((15 * T / 4) * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))) *
          ca ^ 2 * cd ^ 4 * (Q : ℝ) ^ (6 * δ) *
          (((harmonic Q : ℚ) : ℝ)) := by simpa only [Q] using hraw
      _ = (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) *
          ((15 * T / 4) * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))) *
          ca ^ 2 * cd ^ 4 *
          ((Q : ℝ) ^ (6 * δ) * (((harmonic Q : ℚ) : ℝ))) := by ring
      _ ≤ ((100 / δ + 3) ^ 2 * T ^ (2 * δ)) *
          (G * T ^ (1 + δ)) * ca ^ 2 * cd ^ 4 *
          ((1 + δ⁻¹) * (5841 : ℝ) ^ (7 * δ) *
            T ^ (77 * δ)) := by gcongr
      _ = A * T ^ (1 + 80 * δ) := by
        dsimp only [A, G]
        rw [← hpowcombine]
        ring
  have hexp : 1 + 80 * δ ≤ 1 + ε := by
    dsimp only [δ]
    linarith
  have hpow : T ^ (1 + 80 * δ) ≤ T ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hT1 hexp
  have htarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) :=
        (Real.rpow_add hT0 ε 1).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg (hughesYoungActiveFiniteDiagonal T (T / 8)
      (hughesYoungGlobalRadius T) (hughesYoungGlobalDepth T))), htarget]
  exact hbound.trans (mul_le_mul_of_nonneg_left hpow hA)

end RiemannZeta.GuthMaynard
